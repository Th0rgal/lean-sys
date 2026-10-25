//! Zero-dependency typed Rust bindings to the 17 formally verified unboxed C-ABI
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_17_cabi_gates_enforce_tight_bounds() {
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
    }
}
