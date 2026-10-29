//! Zero-dependency typed Rust bindings to all 33 formally verified unboxed C-ABI
//! safety gates in `LeanSys/Spec.lean` (`0 import Lean`, `0 sorryAx`).

extern "C" {
    pub fn leansys_verify_slice_bounds(off: u64, len: u64, cap: u64) -> u8;

    pub fn leansys_verify_wal_frame(
        magic: u32,
        payload_len: u32,
        actual_bytes: u64,
        expected_hash: u64,
        computed_hash: u64,
    ) -> u8;

    pub fn leansys_verify_cas_digest(
        expected_digest: u64,
        computed_digest: u64,
        has_path_sep: u8,
    ) -> u8;

    pub fn leansys_check_http_bounds(
        num_headers: u32,
        content_len: u64,
        actual_body_len: u64,
        auth_ok: u8,
    ) -> u8;

    pub fn leansys_verify_jsonl_tape(
        key_off: u64,
        key_len: u64,
        val_off: u64,
        val_len: u64,
        buf_cap: u64,
        depth: u32,
    ) -> u8;

    pub fn leansys_verify_ring_cursor(head: u64, tail: u64, cap: u64, msg_len: u64) -> u8;

    pub fn leansys_verify_sst_block(
        magic: u32,
        num_entries: u32,
        index_off: u64,
        footer_off: u64,
        file_size: u64,
        bloom_mask: u64,
    ) -> u8;

    pub fn leansys_verify_poll_interest(
        active_conns: u32,
        max_conns: u32,
        keep_alive_reqs: u32,
        max_keep_alive: u32,
        idle_ms: u32,
        max_idle_ms: u32,
    ) -> u8;

    pub fn leansys_verify_rlimit_budget(
        rss_bytes: u64,
        max_rss_bytes: u64,
        elapsed_ms: u64,
        timeout_ms: u64,
        pipe_bytes: u64,
        max_pipe_bytes: u64,
    ) -> u8;

    pub fn leansys_mix64_word(acc: u64, word: u64) -> u64;

    pub fn leansys_verify_composite_key_order(
        hi_a: u64,
        lo_a: u64,
        seq_a: u64,
        hi_b: u64,
        lo_b: u64,
        seq_b: u64,
    ) -> u8;

    pub fn leansys_verify_token_auth(
        match_current: u8,
        has_prev: u8,
        match_prev: u8,
        scope_ok: u8,
        now_epoch: u64,
        expires_at: u64,
    ) -> u8;

    pub fn leansys_verify_log_window(
        start_off: u64,
        next_off: u64,
        file_len: u64,
        max_bytes: u64,
    ) -> u8;

    pub fn leansys_verify_jsonrpc_frame(
        has_v2: u8,
        has_id: u8,
        method_len: u32,
        payload_len: u64,
    ) -> u8;

    pub fn leansys_gate_admit(no_sorry_ax: u8, statement_pinned: u8, cert_verified: u8) -> u8;

    pub fn leansys_verify_mmap_seqlock(
        magic: u32,
        schema_version: u32,
        expected_version: u32,
        seq_before: u64,
        seq_after: u64,
        writer_epoch: u64,
        min_epoch: u64,
        payload_len: u64,
        ring_cap: u64,
    ) -> u8;

    pub fn leansys_verify_proc_stat_fields(
        comm_open_idx: u64,
        comm_close_idx: u64,
        total_len: u64,
        min_fields_after_comm: u64,
        actual_fields: u64,
    ) -> u8;

    pub fn leansys_sse_frame_scan(
        frame_off: u64,
        frame_len: u64,
        chunk_len: u64,
        field_kind: u8,
        next_byte: u8,
        last_byte: u8,
    ) -> u8;

    pub fn leansys_gfm_pipe_scan(
        row_off: u64,
        row_len: u64,
        buf_len: u64,
        col_count: u32,
        sep_cols: u32,
        unterminated_escape: u8,
    ) -> u8;

    pub fn leansys_tag_scan(
        tag_off: u64,
        tag_len: u64,
        attr_off: u64,
        attr_len: u64,
        buf_len: u64,
        tag_kind: u8,
    ) -> u8;

    pub fn leansys_transcript_index(
        turn_off: u64,
        turn_len: u64,
        buf_len: u64,
        prev_digest: u64,
        block_hash: u64,
    ) -> u64;

    pub fn leansys_verify_par_chunk(
        chunk_start: u64,
        chunk_end: u64,
        total_len: u64,
        min_grain: u64,
    ) -> u8;

    pub fn leansys_verify_arena_disjoint(
        off_a: u64,
        len_a: u64,
        off_b: u64,
        len_b: u64,
        arena_cap: u64,
    ) -> u8;

    pub fn leansys_verify_snapshot_visibility(
        entry_seq: u64,
        max_snapshot_seq: u64,
        is_tombstone: u8,
    ) -> u8;

    pub fn leansys_verify_http_route_match(
        method_match: u8,
        path_match: u8,
        route_idx: u32,
        route_count: u32,
    ) -> u8;

    pub fn leansys_verify_counterexample_triage(
        has_violation: u8,
        has_missing_hyp_hint: u8,
        ref_disagrees_with_candidate: u8,
        triage_class: u8,
    ) -> u8;

    pub fn leansys_verify_dag_wave_step(
        in_degree_sum: u64,
        wave_size: u64,
        completed_tasks: u64,
        total_tasks: u64,
        active_workers: u64,
        max_workers: u64,
    ) -> u8;

    pub fn leansys_verify_ios_jetsam_budget(
        dirty_rss_bytes: u64,
        alloc_bytes: u64,
        max_jetsam_bytes: u64,
        page_align_mask: u64,
        is_app_extension: u8,
    ) -> u8;

    pub fn leansys_verify_worker_budget(
        active_workers: u64,
        max_workers: u64,
        micro_chunks: u64,
        total_len: u64,
        topology_kind: u8,
    ) -> u8;

    pub fn leansys_verify_page_aligned_buffer(
        addr: u64,
        alloc_bytes: u64,
        capacity_bytes: u64,
        dirty_rss_bytes: u64,
        max_budget_bytes: u64,
        page_align_mask: u64,
    ) -> u8;

    pub fn leansys_select_isa(
        detected_hw_caps: u64,
        required_mask: u64,
        requested_variant_id: u8,
        max_variant_id: u8,
    ) -> u8;

    pub fn leansys_verify_isa_selection(
        detected_hw_caps: u64,
        required_mask: u64,
        selected_variant_id: u8,
        max_variant_id: u8,
    ) -> u8;

    pub fn leansys_verify_fd_bounds(raw_word: u64, fd_out: u32) -> u8;
}

pub const WAL_MAGIC: u32 = 0x4C53_5953;
pub const SST_MAGIC: u32 = 0x4C53_5354;
pub const MMAP_SEQLOCK_MAGIC: u32 = 0x4C53_4D4D;

#[inline]
pub fn verify_slice_bounds(off: u64, len: u64, cap: u64) -> bool {
    unsafe { leansys_verify_slice_bounds(off, len, cap) == 1 }
}

#[inline]
pub fn verify_wal_frame(
    magic: u32,
    payload_len: u32,
    actual_bytes: u64,
    expected_hash: u64,
    computed_hash: u64,
) -> bool {
    unsafe {
        leansys_verify_wal_frame(
            magic,
            payload_len,
            actual_bytes,
            expected_hash,
            computed_hash,
        ) == 1
    }
}

#[inline]
pub fn verify_cas_digest(expected_digest: u64, computed_digest: u64, has_path_sep: bool) -> bool {
    unsafe {
        leansys_verify_cas_digest(expected_digest, computed_digest, u8::from(has_path_sep)) == 1
    }
}

#[inline]
pub fn check_http_bounds(
    num_headers: u32,
    content_len: u64,
    actual_body_len: u64,
    auth_ok: bool,
) -> bool {
    unsafe {
        leansys_check_http_bounds(num_headers, content_len, actual_body_len, u8::from(auth_ok)) == 1
    }
}

#[inline]
pub fn verify_jsonl_tape(
    key_off: u64,
    key_len: u64,
    val_off: u64,
    val_len: u64,
    buf_cap: u64,
    depth: u32,
) -> bool {
    unsafe { leansys_verify_jsonl_tape(key_off, key_len, val_off, val_len, buf_cap, depth) == 1 }
}

#[inline]
pub fn verify_ring_cursor(head: u64, tail: u64, cap: u64, msg_len: u64) -> bool {
    unsafe { leansys_verify_ring_cursor(head, tail, cap, msg_len) == 1 }
}

#[inline]
pub fn verify_sst_block(
    magic: u32,
    num_entries: u32,
    index_off: u64,
    footer_off: u64,
    file_size: u64,
    bloom_mask: u64,
) -> bool {
    unsafe {
        leansys_verify_sst_block(
            magic,
            num_entries,
            index_off,
            footer_off,
            file_size,
            bloom_mask,
        ) == 1
    }
}

#[inline]
pub fn verify_poll_interest(
    active_conns: u32,
    max_conns: u32,
    keep_alive_reqs: u32,
    max_keep_alive: u32,
    idle_ms: u32,
    max_idle_ms: u32,
) -> bool {
    unsafe {
        leansys_verify_poll_interest(
            active_conns,
            max_conns,
            keep_alive_reqs,
            max_keep_alive,
            idle_ms,
            max_idle_ms,
        ) == 1
    }
}

#[inline]
pub fn verify_rlimit_budget(
    rss_bytes: u64,
    max_rss_bytes: u64,
    elapsed_ms: u64,
    timeout_ms: u64,
    pipe_bytes: u64,
    max_pipe_bytes: u64,
) -> bool {
    unsafe {
        leansys_verify_rlimit_budget(
            rss_bytes,
            max_rss_bytes,
            elapsed_ms,
            timeout_ms,
            pipe_bytes,
            max_pipe_bytes,
        ) == 1
    }
}

#[inline]
pub fn mix64_word(acc: u64, word: u64) -> u64 {
    unsafe { leansys_mix64_word(acc, word) }
}

#[inline]
pub fn verify_composite_key_order(
    hi_a: u64,
    lo_a: u64,
    seq_a: u64,
    hi_b: u64,
    lo_b: u64,
    seq_b: u64,
) -> bool {
    unsafe { leansys_verify_composite_key_order(hi_a, lo_a, seq_a, hi_b, lo_b, seq_b) == 1 }
}

#[inline]
pub fn verify_token_auth(
    match_current: bool,
    has_prev: bool,
    match_prev: bool,
    scope_ok: bool,
    now_epoch: u64,
    expires_at: u64,
) -> bool {
    unsafe {
        leansys_verify_token_auth(
            u8::from(match_current),
            u8::from(has_prev),
            u8::from(match_prev),
            u8::from(scope_ok),
            now_epoch,
            expires_at,
        ) == 1
    }
}

#[inline]
pub fn verify_log_window(start_off: u64, next_off: u64, file_len: u64, max_bytes: u64) -> bool {
    unsafe { leansys_verify_log_window(start_off, next_off, file_len, max_bytes) == 1 }
}

#[inline]
pub fn verify_jsonrpc_frame(has_v2: bool, has_id: bool, method_len: u32, payload_len: u64) -> bool {
    unsafe {
        leansys_verify_jsonrpc_frame(u8::from(has_v2), u8::from(has_id), method_len, payload_len)
            == 1
    }
}

#[inline]
pub fn gate_admit(no_sorry_ax: bool, statement_pinned: bool, cert_verified: bool) -> bool {
    unsafe {
        leansys_gate_admit(
            u8::from(no_sorry_ax),
            u8::from(statement_pinned),
            u8::from(cert_verified),
        ) == 1
    }
}

#[inline]
pub fn verify_mmap_seqlock(
    magic: u32,
    schema_version: u32,
    expected_version: u32,
    seq_before: u64,
    seq_after: u64,
    writer_epoch: u64,
    min_epoch: u64,
    payload_len: u64,
    ring_cap: u64,
) -> bool {
    unsafe {
        leansys_verify_mmap_seqlock(
            magic,
            schema_version,
            expected_version,
            seq_before,
            seq_after,
            writer_epoch,
            min_epoch,
            payload_len,
            ring_cap,
        ) == 1
    }
}

#[inline]
pub fn verify_proc_stat_fields(
    comm_open_idx: u64,
    comm_close_idx: u64,
    total_len: u64,
    min_fields_after_comm: u64,
    actual_fields: u64,
) -> bool {
    unsafe {
        leansys_verify_proc_stat_fields(
            comm_open_idx,
            comm_close_idx,
            total_len,
            min_fields_after_comm,
            actual_fields,
        ) == 1
    }
}

#[inline]
pub fn sse_frame_scan(
    frame_off: u64,
    frame_len: u64,
    chunk_len: u64,
    field_kind: u8,
    next_byte: u8,
    last_byte: u8,
) -> bool {
    unsafe {
        leansys_sse_frame_scan(frame_off, frame_len, chunk_len, field_kind, next_byte, last_byte) == 1
    }
}

#[inline]
pub fn gfm_pipe_scan(
    row_off: u64,
    row_len: u64,
    buf_len: u64,
    col_count: u32,
    sep_cols: u32,
    unterminated_escape: bool,
) -> bool {
    unsafe {
        leansys_gfm_pipe_scan(
            row_off,
            row_len,
            buf_len,
            col_count,
            sep_cols,
            u8::from(unterminated_escape),
        ) == 1
    }
}

#[inline]
pub fn tag_scan(
    tag_off: u64,
    tag_len: u64,
    attr_off: u64,
    attr_len: u64,
    buf_len: u64,
    tag_kind: u8,
) -> bool {
    unsafe { leansys_tag_scan(tag_off, tag_len, attr_off, attr_len, buf_len, tag_kind) == 1 }
}

#[inline]
pub fn transcript_index(
    turn_off: u64,
    turn_len: u64,
    buf_len: u64,
    prev_digest: u64,
    block_hash: u64,
) -> u64 {
    unsafe { leansys_transcript_index(turn_off, turn_len, buf_len, prev_digest, block_hash) }
}

#[inline]
pub fn verify_par_chunk(
    chunk_start: u64,
    chunk_end: u64,
    total_len: u64,
    min_grain: u64,
) -> bool {
    unsafe { leansys_verify_par_chunk(chunk_start, chunk_end, total_len, min_grain) == 1 }
}

#[inline]
pub fn verify_arena_disjoint(
    off_a: u64,
    len_a: u64,
    off_b: u64,
    len_b: u64,
    arena_cap: u64,
) -> bool {
    unsafe { leansys_verify_arena_disjoint(off_a, len_a, off_b, len_b, arena_cap) == 1 }
}

#[inline]
pub fn verify_snapshot_visibility(entry_seq: u64, max_snapshot_seq: u64, is_tombstone: bool) -> bool {
    unsafe {
        leansys_verify_snapshot_visibility(entry_seq, max_snapshot_seq, u8::from(is_tombstone)) == 1
    }
}

#[inline]
pub fn verify_http_route_match(
    method_match: bool,
    path_match: bool,
    route_idx: u32,
    route_count: u32,
) -> bool {
    unsafe {
        leansys_verify_http_route_match(
            u8::from(method_match),
            u8::from(path_match),
            route_idx,
            route_count,
        ) == 1
    }
}

#[inline]
pub fn verify_counterexample_triage(
    has_violation: bool,
    has_missing_hyp_hint: bool,
    ref_disagrees_with_candidate: bool,
    triage_class: u8,
) -> bool {
    unsafe {
        leansys_verify_counterexample_triage(
            u8::from(has_violation),
            u8::from(has_missing_hyp_hint),
            u8::from(ref_disagrees_with_candidate),
            triage_class,
        ) == 1
    }
}

#[inline]
pub fn verify_dag_wave_step(
    in_degree_sum: u64,
    wave_size: u64,
    completed_tasks: u64,
    total_tasks: u64,
    active_workers: u64,
    max_workers: u64,
) -> bool {
    unsafe {
        leansys_verify_dag_wave_step(
            in_degree_sum,
            wave_size,
            completed_tasks,
            total_tasks,
            active_workers,
            max_workers,
        ) == 1
    }
}

#[inline]
pub fn verify_ios_jetsam_budget(
    dirty_rss_bytes: u64,
    alloc_bytes: u64,
    max_jetsam_bytes: u64,
    page_align_mask: u64,
    is_app_extension: bool,
) -> bool {
    unsafe {
        leansys_verify_ios_jetsam_budget(
            dirty_rss_bytes,
            alloc_bytes,
            max_jetsam_bytes,
            page_align_mask,
            u8::from(is_app_extension),
        ) == 1
    }
}

#[inline]
pub fn verify_worker_budget(
    active_workers: u64,
    max_workers: u64,
    micro_chunks: u64,
    total_len: u64,
    topology_kind: u8,
) -> bool {
    unsafe {
        leansys_verify_worker_budget(
            active_workers,
            max_workers,
            micro_chunks,
            total_len,
            topology_kind,
        ) == 1
    }
}

#[inline]
pub fn verify_page_aligned_buffer(
    addr: u64,
    alloc_bytes: u64,
    capacity_bytes: u64,
    dirty_rss_bytes: u64,
    max_budget_bytes: u64,
    page_align_mask: u64,
) -> bool {
    unsafe {
        leansys_verify_page_aligned_buffer(
            addr,
            alloc_bytes,
            capacity_bytes,
            dirty_rss_bytes,
            max_budget_bytes,
            page_align_mask,
        ) == 1
    }
}

#[inline]
pub fn select_isa(
    detected_hw_caps: u64,
    required_mask: u64,
    requested_variant_id: u8,
    max_variant_id: u8,
) -> u8 {
    unsafe {
        leansys_select_isa(
            detected_hw_caps,
            required_mask,
            requested_variant_id,
            max_variant_id,
        )
    }
}

#[inline]
pub fn verify_isa_selection(
    detected_hw_caps: u64,
    required_mask: u64,
    selected_variant_id: u8,
    max_variant_id: u8,
) -> bool {
    unsafe {
        leansys_verify_isa_selection(
            detected_hw_caps,
            required_mask,
            selected_variant_id,
            max_variant_id,
        ) == 1
    }
}

#[inline]
pub fn verify_fd_bounds(raw_word: u64, fd_out: u32) -> bool {
    unsafe { leansys_verify_fd_bounds(raw_word, fd_out) == 1 }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_33_cabi_gates_enforce_tight_bounds() {
        assert!(verify_slice_bounds(4, 8, 12));
        assert!(!verify_slice_bounds(5, 8, 12));

        assert!(verify_wal_frame(WAL_MAGIC, 16, 16, 0xCAFE, 0xCAFE));
        assert!(!verify_wal_frame(WAL_MAGIC, 16, 15, 0xCAFE, 0xCAFE));

        assert!(verify_cas_digest(42, 42, false));
        assert!(!verify_cas_digest(42, 42, true));

        assert!(check_http_bounds(8, 128, 128, true));
        assert!(!check_http_bounds(8, 128, 128, false));

        assert!(verify_jsonl_tape(0, 4, 5, 6, 16, 2));
        assert!(!verify_jsonl_tape(0, 8, 4, 6, 16, 2));

        assert!(verify_ring_cursor(20, 10, 64, 16));
        assert!(!verify_ring_cursor(20, 10, 16, 16));

        assert!(verify_sst_block(SST_MAGIC, 3, 64, 128, 160, 0x11));
        assert!(!verify_sst_block(SST_MAGIC, 3, 64, 128, 160, 0));

        assert!(verify_poll_interest(4, 64, 2, 16, 100, 5000));
        assert!(!verify_poll_interest(65, 64, 2, 16, 100, 5000));

        assert!(verify_rlimit_budget(1024, 2048, 50, 100, 256, 512));
        assert!(!verify_rlimit_budget(4096, 2048, 50, 100, 256, 512));

        assert_ne!(mix64_word(0, 0), mix64_word(0, 1));

        assert!(verify_composite_key_order(1, 2, 3, 1, 2, 4));
        assert!(!verify_composite_key_order(1, 3, 0, 1, 2, 9));

        assert!(verify_token_auth(false, true, true, true, 100, 200));
        assert!(!verify_token_auth(false, true, true, true, 200, 200));

        assert!(verify_log_window(100, 500, 1000, 65536));
        assert!(!verify_log_window(500, 100, 1000, 65536));

        assert!(verify_jsonrpc_frame(true, true, 12, 512));
        assert!(!verify_jsonrpc_frame(false, true, 12, 512));

        assert!(gate_admit(true, true, true));
        assert!(!gate_admit(true, false, true));

        assert!(verify_mmap_seqlock(
            MMAP_SEQLOCK_MAGIC,
            1,
            1,
            4,
            4,
            10,
            10,
            64,
            256
        ));
        assert!(!verify_mmap_seqlock(
            MMAP_SEQLOCK_MAGIC,
            1,
            1,
            5,
            5,
            10,
            10,
            64,
            256
        ));

        assert!(verify_proc_stat_fields(5, 18, 120, 20, 35));
        assert!(!verify_proc_stat_fields(18, 5, 120, 20, 35));

        assert!(sse_frame_scan(4, 12, 64, 2, 0x41, 0x7D));
        assert!(!sse_frame_scan(4, 12, 64, 2, 0x85, 0x7D));
        assert!(!sse_frame_scan(4, 12, 64, 2, 0x41, 0xE2));
        assert!(!sse_frame_scan(u64::MAX - 7, 16, 64, 2, 0x41, 0x7D));

        assert!(gfm_pipe_scan(0, 24, 64, 3, 3, false));
        assert!(!gfm_pipe_scan(0, 24, 64, 3, 2, false));
        assert!(!gfm_pipe_scan(0, 24, 64, 3, 3, true));

        assert!(tag_scan(0, 20, 6, 12, 64, 1));
        assert!(!tag_scan(0, 20, 6, 18, 64, 1));
        assert!(!tag_scan(0, 20, 6, u64::MAX - 3, 64, 1));

        assert_ne!(transcript_index(0, 32, 64, 0x1111, 0x2222), 0);
        assert_eq!(transcript_index(48, 32, 64, 0x1111, 0x2222), 0);

        assert!(verify_par_chunk(0, 64, 256, 64));
        assert!(!verify_par_chunk(0, 32, 256, 64));

        assert!(verify_arena_disjoint(0, 128, 128, 128, 256));
        assert!(!verify_arena_disjoint(0, 128, 64, 128, 256));

        assert!(verify_snapshot_visibility(2, 5, false));
        assert!(!verify_snapshot_visibility(6, 5, false));
        assert!(!verify_snapshot_visibility(2, 5, true));

        assert!(verify_http_route_match(true, true, 0, 4));
        assert!(!verify_http_route_match(false, true, 0, 4));
        assert!(!verify_http_route_match(true, true, 4, 4));
        assert!(!verify_http_route_match(true, true, 0, 65));

        assert!(verify_counterexample_triage(true, true, false, 1));
        assert!(verify_counterexample_triage(true, false, true, 2));
        assert!(verify_counterexample_triage(true, false, false, 3));
        assert!(!verify_counterexample_triage(true, true, false, 3));
        assert!(!verify_counterexample_triage(false, true, false, 1));

        assert!(verify_dag_wave_step(0, 4, 8, 16, 4, 4));
        assert!(!verify_dag_wave_step(1, 4, 8, 16, 4, 4));
        assert!(!verify_dag_wave_step(0, 12, 8, 16, 4, 4));

        assert!(verify_ios_jetsam_budget(4_194_304, 65_536, 134_217_728, 16_383, false));
        assert!(verify_ios_jetsam_budget(4_194_304, 65_536, 25_165_824, 16_383, true));
        assert!(!verify_ios_jetsam_budget(4_194_304, 65_536, 33_554_432, 16_383, true));

        assert!(verify_worker_budget(4, 6, 24, 4096, 1));
        assert!(!verify_worker_budget(4, 8, 24, 4096, 1));
        assert!(verify_worker_budget(6, 9, 54, 4096, 2));
        assert!(!verify_worker_budget(6, 10, 54, 4096, 2));

        assert!(verify_page_aligned_buffer(
            0x10000,
            4096,
            16_384,
            1_048_576,
            134_217_728,
            16_383
        ));
        assert!(!verify_page_aligned_buffer(
            0x11000,
            4096,
            16_384,
            1_048_576,
            134_217_728,
            16_383
        ));

        assert_eq!(select_isa(0x37F, 0x37F, 3, 3), 3);
        assert_eq!(select_isa(0x307, 0x37F, 3, 3), 0);
        assert_eq!(select_isa(0x37F, 0, 3, 3), 0);

        assert!(verify_isa_selection(0x37F, 0x37F, 3, 3));
        assert!(!verify_isa_selection(0x307, 0x37F, 3, 3));
        assert!(!verify_isa_selection(0x37F, 0x107, 3, 3));

        assert!(verify_fd_bounds(70_000, 70_000));
        assert!(verify_fd_bounds(0x7FFF_FFFF, 0x7FFF_FFFF));
        assert!(!verify_fd_bounds(0x8000_0000, 0x8000_0000));
        assert!(!verify_fd_bounds(70_000, 4_464));
    }
}
