/*

Copyright (c) 2017, BitTorrent Inc.
Copyright (c) 2019-2021, Arvid Norberg
Copyright (c) 2019-2020, Steven Siloti
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in
the documentation and/or other materials provided with the distribution.
* Neither the name of the author nor the names of its
contributors may be used to endorse or promote products derived
from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

#include "libtorrent/hash_picker.hpp"
#include "libtorrent/aux_/merkle.hpp"
#include "libtorrent/peer_connection.hpp"
#include "libtorrent/aux_/numeric_cast.hpp"

namespace libtorrent
{
	namespace
	{
		time_duration const min_request_interval = seconds(3);
		int const bucket_piece_span = 512;
	}

/*
merkle tree for a file:

             ^            x
proof_layer  |    x                x
       ^      x       [****************]
       |    x   x   x   x    x   x   x   x
  base |   x x x x x x x x  x x x x x x x x  <- block hash layer, leaves
              ------->
              index
                      ----------------->
                      count
*/

bool validate_hash_request(hash_request const& hr, file_storage const& fs)
{
	// limit the size of the base layer to something reasonable
	// Blocks are requested for an entire piece so this limit
	// effectively caps the piece size we can handle. A limit of 8192
	// corresponds to a piece size of 128MB.

	if (hr.file < file_index_t{0}
		|| hr.file >= fs.end_file()
		|| hr.base < 0
		|| hr.index < 0
		|| hr.count <= 0
		|| hr.count > 8192
		|| hr.proof_layers < 0)
		return false;

	int const num_leafs = merkle_num_leafs(fs.file_num_blocks(hr.file));
	int const num_layers = merkle_num_layers(num_leafs);

	if (hr.base >= num_layers) return false;

	// the number of hashes at the specified level
	int const level_size = num_leafs >> hr.base;

	// [index, index + count] must be within the number of nodes at the specified
	// level
	if (hr.index >= level_size || hr.index + hr.count > level_size)
		return false;

	if (hr.proof_layers >= num_layers - hr.base) return false;

	return true;
}

	hash_picker::hash_picker(file_storage const& files
		, aux::vector<aux::merkle_tree, file_index_t>& trees)
		: m_files(files)
		, m_merkle_trees(trees)
		, m_piece_layer(merkle_num_layers(files.piece_length() / default_block_size))
		, m_piece_tree_root_layer(m_piece_layer + merkle_num_layers(512))
	{
		m_piece_hash_requested.resize(trees.size());
		for (file_index_t f(0); f != m_files.end_file(); ++f)
		{
			if (m_files.pad_file_at(f)) continue;

			auto const& tree = m_merkle_trees[f];
			auto const v = tree.verified_leafs();

			if (m_files.file_size(f) <= m_files.piece_length())
				continue;

			m_piece_hash_requested[f].resize((m_files.file_num_pieces(f) + 511) / 512);

			int const piece_layer_idx = merkle_num_layers(
				merkle_num_leafs(m_files.file_num_blocks(f))) - m_piece_layer;
			int const piece_layer_start = merkle_layer_start(piece_layer_idx);

			// check for hashes we already have and flag entries in m_piece_hash_requested
			// so that we don't request them again
			for (int i = 0; i < int(m_piece_hash_requested[f].size()); ++i)
			{
				for (int j = i * 512;; ++j)
				{
					if (j == (i + 1) * 512 || j >= m_files.file_num_pieces(f))
					{
						m_piece_hash_requested[f][i].have = true;
						break;
					}
					if ((m_files.piece_length() == default_block_size && !v[std::size_t(j)])
						|| (m_files.piece_length() > default_block_size
							&& !tree.has_node(piece_layer_start + j)))
						break;
				}
			}
		}
	}

	hash_request hash_picker::pick_hashes(typed_bitfield<piece_index_t> const& pieces
		, torrent_peer* peer)
	{
		TORRENT_UNUSED(pieces);
		auto const now = aux::time_now();

		// this is for a future per-block request feature
#if 0
		if (!m_priority_block_requests.empty())
		{
			auto& req = m_priority_block_requests.front();
			node_index const nidx(req.file, m_files.file_first_block_node(req.file) + req.block);
			hash_request hash_req(req.file
				, 0
				, req.block
				, 2
				, layers_to_verify(nidx) + 1);
			req.num_requests++;
			std::sort(m_priority_block_requests.begin(), m_priority_block_requests.end());
			return hash_req;
		}
#endif

		if (!m_piece_block_requests.empty())
		{
			auto const req = std::find_if(m_piece_block_requests.begin(), m_piece_block_requests.end()
				, [now](piece_block_request const& e)
					{ return e.last_request == min_time() || e.last_request - now > min_request_interval; });
			if (req != m_piece_block_requests.end())
			{
				int const blocks_per_piece = m_files.piece_length() / default_block_size;

				// number of blocks from the start of the file
				int const first_block = static_cast<int>(req->piece) * blocks_per_piece;
				node_index const nidx(req->file, m_files.file_first_block_node(req->file) + first_block);
				hash_request hash_req(req->file
					, 0
					, first_block
					, blocks_per_piece
					, layers_to_verify(nidx) + merkle_num_layers(blocks_per_piece));
				req->num_requests++;
				req->last_request = now;
				std::sort(m_piece_block_requests.begin(), m_piece_block_requests.end());
				return hash_req;
			}
		}

		if (peer == nullptr) return {};

		update_ready_buckets(now);

		if (m_peer_buckets.find(peer) == m_peer_buckets.end()) return {};

		while (!m_bucket_queue.empty())
		{
			auto entry = m_bucket_queue.top();
			m_bucket_queue.pop();

			auto& state = bucket_state(entry.file, entry.bucket);
			if (!state.queued || entry.generation != state.generation)
				continue;
			if (state.have || state.availability == 0)
			{
				cancel_bucket(entry.file, entry.bucket);
				continue;
			}
			if (state.pending)
				continue;
			if (!peer_has_bucket(peer, entry.file, entry.bucket))
			{
				m_bucket_queue.push(entry);
				break;
			}

			state.queued = false;
			state.pending = true;
			state.last_request = now;
			state.next_request = now + min_request_interval;
			++state.num_requests;

			schedule_bucket(entry.file, entry.bucket, state.next_request, now);

			if (m_files.pad_file_at(entry.file) || m_files.file_size(entry.file) == 0)
				continue;

			int const num_layers = file_num_layers(entry.file);
			int const piece_tree_root_layer = std::max(0, num_layers - m_piece_tree_root_layer);
			int const piece_tree_root_start = merkle_layer_start(piece_tree_root_layer);
			int const piece_tree_root = piece_tree_root_start + entry.bucket;
			int const piece_tree_num_layers
				= num_layers - piece_tree_root_layer - m_piece_layer;

			int const remaining_pieces = int(m_files.file_num_pieces(entry.file) - entry.bucket * bucket_piece_span);

			return hash_request(entry.file
				, m_piece_layer
				, entry.bucket * bucket_piece_span
				, std::min(bucket_piece_span, merkle_num_leafs(remaining_pieces))
				, layers_to_verify({ entry.file, piece_tree_root }) + piece_tree_num_layers);
		}

		return {};
	}

	add_hashes_result hash_picker::add_hashes(hash_request const& req, span<sha256_hash const> hashes)
	{
		TORRENT_ASSERT(validate_hash_request(req, m_files));

		int const unpadded_count = std::min(req.count, m_files.file_num_pieces(req.file) - req.index);
		int const leaf_count = merkle_num_leafs(req.count);
		int const base_num_layers = merkle_num_layers(leaf_count);
		int const num_uncle_hashes = std::max(0, req.proof_layers - base_num_layers + 1);

		if (req.count + num_uncle_hashes != hashes.size())
			return add_hashes_result(false);

		// for now we rely on only requesting piece hashes in 512 chunks
		if (req.base == m_piece_layer
			&& req.count != 512
			&& (req.count > 512 || unpadded_count != m_files.file_num_pieces(req.file) - req.index))
			return add_hashes_result(false);

		// for now we only support receiving hashes at the piece and leaf layers
		if (req.base != m_piece_layer && req.base != 0)
			return add_hashes_result(false);

		// the incoming list of hashes is really two separate lists, the lowest
		// layer of hashes we requested (typically the block- or piece layer).
		// There are req.count of those, then there are the uncle hashes
		// required to prove the correctness of the first hashes, to anchor the
		// new hashes in the existing tree
		auto const uncle_hashes = hashes.subspan(req.count);
		hashes = hashes.first(req.count);

		TORRENT_ASSERT(uncle_hashes.size() == num_uncle_hashes);

		int const base_layer_idx = file_num_layers(req.file) - req.base;

		if (base_layer_idx <= 0)
			return add_hashes_result(false);

		add_hashes_result ret(true);

		auto& dst_tree = m_merkle_trees[req.file];
		int const dest_start_idx = merkle_to_flat_index(base_layer_idx, req.index);
		auto const file_piece_offset = m_files.piece_index_at_file(req.file) - piece_index_t{0};
		auto results = dst_tree.add_hashes(dest_start_idx, file_piece_offset, hashes, uncle_hashes);

		if (!results)
			return add_hashes_result(false);

		ret.hash_failed = std::move(results->failed);
		ret.hash_passed = std::move(results->passed);

		if (req.base == m_piece_layer)
		{
			TORRENT_ASSERT(req.index % bucket_piece_span == 0);
			complete_bucket(req.file, req.index / bucket_piece_span);
		}

		return ret;
	}

	set_block_hash_result hash_picker::set_block_hash(piece_index_t const piece
		, int const offset, sha256_hash const& h)
	{
		TORRENT_ASSERT(offset >= 0);
		auto const f = m_files.file_index_at_piece(piece);

		if (m_files.pad_file_at(f))
			return { set_block_hash_result::result::success, 0, 0 };

		auto& merkle_tree = m_merkle_trees[f];
		piece_index_t const file_first_piece = m_files.piece_index_at_file(f);
		std::int64_t const block_offset = static_cast<int>(piece) * std::int64_t(m_files.piece_length())
			+ offset - m_files.file_offset(f);
		int const block_index = aux::numeric_cast<int>(block_offset / default_block_size);

		if (h.is_all_zeros())
		{
			TORRENT_ASSERT_FAIL();
			return set_block_hash_result::block_hash_failed();
		}

		// TODO: use structured bindings in C++17
		aux::merkle_tree::set_block_result result;
		int leafs_index;
		int leafs_size;
		std::tie(result, leafs_index, leafs_size) = merkle_tree.set_block(block_index, h);

		if (result == aux::merkle_tree::set_block_result::unknown)
			return set_block_hash_result::unknown();
		if (result == aux::merkle_tree::set_block_result::block_hash_failed)
			return set_block_hash_result::block_hash_failed();

		auto const status = (result == aux::merkle_tree::set_block_result::hash_failed)
			? set_block_hash_result::result::piece_hash_failed
			: set_block_hash_result::result::success;

		int const blocks_per_piece = m_files.piece_length() / default_block_size;

		return { status
			, int(leafs_index - static_cast<int>(piece - file_first_piece) * blocks_per_piece)
			, std::min(leafs_size, m_files.file_num_pieces(f) * blocks_per_piece - leafs_index) };
	}

	void hash_picker::hashes_rejected(hash_request const& req)
	{
		// We only track piece-layer hash requests (512-piece buckets) in
		// m_piece_hash_requested. Block-level rejections (base != m_piece_layer)
		// or misaligned requests are not represented there, so bail out to avoid
		// out-of-bounds access.
		if (req.base != m_piece_layer || req.index % bucket_piece_span != 0)
			return;

		auto const now = aux::time_now();

		for (int i = req.index; i < req.index + req.count; i += bucket_piece_span)
		{
			int const bucket = i / bucket_piece_span;
			if (req.file < file_index_t(0) || req.file >= m_piece_hash_requested.end_index())
				return;
			if (bucket < 0 || bucket >= int(m_piece_hash_requested[req.file].size()))
				return;
			auto& state = bucket_state(req.file, bucket);
			state.last_request = min_time();
			state.pending = false;
			if (state.num_requests > 0) --state.num_requests;
			if (state.have || state.availability == 0) continue;
			reschedule_bucket(req.file, bucket, now, now);
		}

		// this is for a future per-block request feature
#if 0
		else if (req.base == 0)
		{
			priority_block_request block_req(req.file, req.index);
			auto const existing_req = std::find(
				m_priority_block_requests.begin()
				, m_priority_block_requests.end()
				, block_req);

			if (existing_req == m_priority_block_requests.end())
			{
				m_priority_block_requests.insert(m_priority_block_requests.begin()
					, priority_block_request(req.file, req.index));
			}
		}
#endif
	}

	void hash_picker::peer_has(piece_index_t const index, torrent_peer* peer)
	{
		if (peer == nullptr) return;
		add_piece_for_peer(index, peer, aux::time_now());
	}

	void hash_picker::peer_has(typed_bitfield<piece_index_t> const& bits, torrent_peer* peer)
	{
		if (peer == nullptr) return;
		auto const now = aux::time_now();
		for (auto const piece : bits.range())
		{
			if (!bits[piece]) continue;
			add_piece_for_peer(piece, peer, now);
		}
	}

	void hash_picker::peer_has_all(torrent_peer* peer)
	{
		if (peer == nullptr) return;
		auto const now = aux::time_now();
		auto& state = ensure_peer_state(peer);
		for (auto const f : m_piece_hash_requested.range())
		{
			auto& counts = state.bucket_counts[f];
			for (int bucket = 0; bucket < int(counts.size()); ++bucket)
			{
				std::uint16_t const new_count = std::uint16_t(bucket_piece_count(f, bucket));
				if (new_count == 0) continue;
				bool const had = counts[bucket] > 0;
				counts[bucket] = new_count;
				if (!had)
					inc_bucket_availability(f, bucket, now);
			}
		}
	}

	void hash_picker::peer_lost(piece_index_t const index, torrent_peer* peer)
	{
		if (peer == nullptr) return;
		remove_piece_for_peer(index, peer);
	}

	void hash_picker::peer_lost(typed_bitfield<piece_index_t> const& bits, torrent_peer* peer)
	{
		if (peer == nullptr) return;
		for (auto const piece : bits.range())
		{
			if (!bits[piece]) continue;
			remove_piece_for_peer(piece, peer);
		}
	}

	void hash_picker::peer_lost_all(torrent_peer* peer)
	{
		if (peer == nullptr) return;
		auto const it = m_peer_buckets.find(peer);
		if (it == m_peer_buckets.end()) return;
		for (auto const f : m_piece_hash_requested.range())
		{
			auto& counts = it->second.bucket_counts[f];
			for (int bucket = 0; bucket < int(counts.size()); ++bucket)
			{
				if (counts[bucket] == 0) continue;
				counts[bucket] = 0;
				dec_bucket_availability(f, bucket);
			}
		}
	}

	void hash_picker::remove_peer(torrent_peer* peer)
	{
		if (peer == nullptr) return;
		peer_lost_all(peer);
		m_peer_buckets.erase(peer);
	}

	void hash_picker::verify_block_hashes(piece_index_t const index)
	{
		file_index_t const fidx = m_files.file_index_at_piece(index);
		piece_index_t::diff_type const piece = index - m_files.piece_index_at_file(fidx);
		piece_block_request req(fidx, piece);

		if (std::find(m_piece_block_requests.begin(), m_piece_block_requests.end(), req)
			!= m_piece_block_requests.end())
			return; // already requested

		m_piece_block_requests.insert(m_piece_block_requests.begin(), req);
	}

	bool hash_picker::have_hash(piece_index_t const index) const
	{
		file_index_t const f = m_files.file_index_at_piece(index);
		if (m_files.file_size(f) <= m_files.piece_length()) return true;
		piece_index_t const file_first_piece(int(m_files.file_offset(f) / m_files.piece_length()));
		return m_merkle_trees[f].has_node(m_files.file_first_piece_node(f) + int(index - file_first_piece));
	}

	bool hash_picker::have_all(file_index_t const file) const
	{
		return m_merkle_trees[file].is_complete();
	}

	bool hash_picker::have_all() const
	{
		for (file_index_t f : m_files.file_range())
			if (!have_all(f)) return false;
		return true;
	}

	bool hash_picker::piece_verified(piece_index_t const piece) const
	{
		file_index_t const f = m_files.file_index_at_piece(piece);
		piece_index_t const file_first_piece(int(m_files.file_offset(f) / m_files.piece_length()));
		int const block_offset = static_cast<int>(piece - file_first_piece) * (m_files.piece_length() / default_block_size);
		int const blocks_in_piece = m_files.blocks_in_piece2(piece);
		return m_merkle_trees[f].blocks_verified(block_offset, blocks_in_piece);
	}

	int hash_picker::layers_to_verify(node_index idx) const
	{
		// the root layer doesn't have a sibling so it should never
		// be requested as a proof layer
		// return -1 to signal to the caller that no proof is required
		// even for the first layer it is trying to verify
		if (idx.node == 0) return -1;

		int layers = 0;
		int const file_internal_layers = merkle_num_layers(merkle_num_leafs(m_files.file_num_pieces(idx.file))) - 1;
		auto const& tree = m_merkle_trees[idx.file];

		for (;;)
		{
			idx.node = merkle_get_parent(idx.node);
			if (tree.has_node(idx.node)) break;
			layers++;
			if (layers == file_internal_layers) return layers;
		}

		return layers;
	}

	int hash_picker::file_num_layers(file_index_t const idx) const
	{
		return merkle_num_layers(merkle_num_leafs(m_files.file_num_blocks(idx)));
	}

	hash_picker::piece_hash_request& hash_picker::bucket_state(file_index_t const file, int const bucket)
	{
		TORRENT_ASSERT(bucket >= 0);
		return m_piece_hash_requested[file][bucket];
	}

	hash_picker::piece_hash_request const& hash_picker::bucket_state(file_index_t const file, int const bucket) const
	{
		TORRENT_ASSERT(bucket >= 0);
		return m_piece_hash_requested[file][bucket];
	}

	void hash_picker::update_ready_buckets(time_point const now)
	{
		while (!m_waiting_buckets.empty())
		{
			auto const tb = m_waiting_buckets.top();
			if (tb.ready_time > now) break;
			m_waiting_buckets.pop();

			auto& state = bucket_state(tb.entry.file, tb.entry.bucket);
			if (!state.queued || tb.entry.generation != state.generation)
				continue;
			if (state.have || state.availability == 0)
			{
				cancel_bucket(tb.entry.file, tb.entry.bucket);
				continue;
			}

			state.pending = false;
			enqueue_bucket(tb.entry);
		}
	}

	void hash_picker::enqueue_bucket(bucket_queue_entry const& entry)
	{
		m_bucket_queue.push(entry);
	}

	void hash_picker::schedule_bucket(file_index_t const file, int const bucket
		, time_point const ready, time_point const now)
	{
		auto& state = bucket_state(file, bucket);
		++state.generation;
		state.queued = true;
		state.next_request = ready;
		bucket_queue_entry entry{ file, bucket, state.generation };
		if (ready <= now)
			enqueue_bucket(entry);
		else
			m_waiting_buckets.push({ ready, entry });
	}

	void hash_picker::reschedule_bucket(file_index_t const file, int const bucket
		, time_point const ready, time_point const now)
	{
		cancel_bucket(file, bucket);
		schedule_bucket(file, bucket, ready, now);
	}

	void hash_picker::cancel_bucket(file_index_t const file, int const bucket)
	{
		auto& state = bucket_state(file, bucket);
		if (!state.queued) return;
		++state.generation;
		state.queued = false;
	}

	void hash_picker::activate_bucket(file_index_t const file, int const bucket
		, time_point const ready, time_point const now)
	{
		auto& state = bucket_state(file, bucket);
		if (state.have || state.pending || state.availability == 0) return;
		if (state.queued)
		{
			if (ready < state.next_request)
				reschedule_bucket(file, bucket, ready, now);
			return;
		}
		schedule_bucket(file, bucket, ready, now);
	}

	void hash_picker::complete_bucket(file_index_t const file, int const bucket)
	{
		auto& state = bucket_state(file, bucket);
		state.have = true;
		state.pending = false;
		cancel_bucket(file, bucket);
	}

	bool hash_picker::bucket_for_piece(piece_index_t const piece
		, file_index_t& file, int& bucket) const
	{
		file = m_files.file_index_at_piece(piece);
		if (m_files.pad_file_at(file)) return false;
		if (m_piece_hash_requested[file].empty()) return false;
		auto const first_piece = m_files.piece_index_at_file(file);
		auto const offset = static_cast<int>(piece - first_piece);
		if (offset < 0) return false;
		bucket = offset / bucket_piece_span;
		if (bucket < 0 || bucket >= int(m_piece_hash_requested[file].size())) return false;
		return true;
	}

	void hash_picker::add_piece_for_peer(piece_index_t const piece, torrent_peer* peer
		, time_point const now)
	{
		file_index_t file;
		int bucket;
		if (!bucket_for_piece(piece, file, bucket)) return;
		auto& state = ensure_peer_state(peer);
		auto& counts = state.bucket_counts[file];
		if (counts.empty())
			counts.resize(m_piece_hash_requested[file].size());
		std::uint16_t& slot = counts[bucket];
		bool const had = slot > 0;
		++slot;
		if (!had)
			inc_bucket_availability(file, bucket, now);
	}

	void hash_picker::remove_piece_for_peer(piece_index_t const piece, torrent_peer* peer)
	{
		auto const it = m_peer_buckets.find(peer);
		if (it == m_peer_buckets.end()) return;
		file_index_t file;
		int bucket;
		if (!bucket_for_piece(piece, file, bucket)) return;
		auto& counts = it->second.bucket_counts[file];
		if (bucket < 0 || bucket >= int(counts.size())) return;
		if (counts[bucket] == 0) return;
		--counts[bucket];
		if (counts[bucket] == 0)
			dec_bucket_availability(file, bucket);
	}

	void hash_picker::inc_bucket_availability(file_index_t const file, int const bucket
		, time_point const now)
	{
		auto& state = bucket_state(file, bucket);
		++state.availability;
		if (state.availability == 1)
			activate_bucket(file, bucket, now, now);
	}

	void hash_picker::dec_bucket_availability(file_index_t const file, int const bucket)
	{
		auto& state = bucket_state(file, bucket);
		TORRENT_ASSERT(state.availability > 0);
		--state.availability;
		if (state.availability == 0)
			cancel_bucket(file, bucket);
	}

	bool hash_picker::peer_has_bucket(torrent_peer* peer, file_index_t const file, int const bucket) const
	{
		auto const it = m_peer_buckets.find(peer);
		if (it == m_peer_buckets.end()) return false;
		auto const& counts = it->second.bucket_counts[file];
		if (bucket < 0 || bucket >= int(counts.size())) return false;
		return counts[bucket] > 0;
	}

	hash_picker::peer_state& hash_picker::ensure_peer_state(torrent_peer* peer)
	{
		auto ret = m_peer_buckets.emplace(peer, peer_state{});
		auto& state = ret.first->second;
		if (ret.second)
		{
			state.bucket_counts.resize(m_piece_hash_requested.size());
			for (auto const f : m_piece_hash_requested.range())
				state.bucket_counts[f].resize(m_piece_hash_requested[f].size());
		}
		return state;
	}

	int hash_picker::bucket_piece_count(file_index_t const file, int const bucket) const
	{
		int const pieces_in_file = int(m_files.file_num_pieces(file));
		int const start = bucket * bucket_piece_span;
		if (start >= pieces_in_file) return 0;
		return std::min(bucket_piece_span, pieces_in_file - start);
	}
}
