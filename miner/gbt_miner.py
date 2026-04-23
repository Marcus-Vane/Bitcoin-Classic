#!/usr/bin/env python3
"""
GBT solo miner for a Bitcoin Core-derived node.

Mines indefinitely by:
  getblocktemplate -> build coinbase (+ witness commitment) -> grind PoW -> submitblock

Designed for development/private networks with easy PoW.
Python stdlib only.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import http.client
import json
import os
import random
import struct
import sys
import time
from dataclasses import dataclass
from typing import Any, Optional


def sha256d(b: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(b).digest()).digest()


def varint(n: int) -> bytes:
    if n < 0:
        raise ValueError("varint negative")
    if n < 0xFD:
        return bytes([n])
    if n <= 0xFFFF:
        return b"\xFD" + struct.pack("<H", n)
    if n <= 0xFFFFFFFF:
        return b"\xFE" + struct.pack("<I", n)
    return b"\xFF" + struct.pack("<Q", n)


def compact_to_target(nbits: int) -> int:
    exp = (nbits >> 24) & 0xFF
    mant = nbits & 0x007FFFFF
    if nbits & 0x00800000:
        raise ValueError("negative compact")
    if exp <= 3:
        return mant >> (8 * (3 - exp))
    return mant << (8 * (exp - 3))


def serialize_scriptnum(value: int) -> bytes:
    # Matches CScriptNum::serialize in src/script/script.h
    if value == 0:
        return b""
    neg = value < 0
    absvalue = (~value + 1) & 0xFFFFFFFFFFFFFFFF if neg else value
    out = bytearray()
    while absvalue:
        out.append(absvalue & 0xFF)
        absvalue >>= 8
    if out[-1] & 0x80:
        out.append(0x80 if neg else 0x00)
    elif neg:
        out[-1] |= 0x80
    return bytes(out)


def script_push(data: bytes) -> bytes:
    l = len(data)
    if l < 0x4C:
        return bytes([l]) + data
    if l <= 0xFF:
        return b"\x4c" + bytes([l]) + data  # OP_PUSHDATA1
    if l <= 0xFFFF:
        return b"\x4d" + struct.pack("<H", l) + data  # OP_PUSHDATA2
    return b"\x4e" + struct.pack("<I", l) + data  # OP_PUSHDATA4


def encode_script_int64(n: int) -> bytes:
    # Matches CScript::push_int64 in src/script/script.h
    if n == 0:
        return b"\x00"  # OP_0
    if 1 <= n <= 16:
        return bytes([0x50 + n])  # OP_1 .. OP_16
    return script_push(serialize_scriptnum(n))


def merkle_root_le(txids_le: list[bytes]) -> bytes:
    if not txids_le:
        return b"\x00" * 32
    level = txids_le[:]
    while len(level) > 1:
        if len(level) % 2 == 1:
            level.append(level[-1])
        nxt: list[bytes] = []
        for i in range(0, len(level), 2):
            nxt.append(sha256d(level[i] + level[i + 1]))
        level = nxt
    return level[0]


def ser_uint256_le_from_hex_be(h: str) -> bytes:
    b = bytes.fromhex(h)
    if len(b) != 32:
        raise ValueError("expected 32-byte hex")
    return b[::-1]


def now() -> int:
    return int(time.time())


class RPCError(RuntimeError):
    def __init__(self, msg: str, code: Optional[int] = None):
        super().__init__(msg)
        self.code = code


@dataclass(frozen=True)
class RPCConfig:
    host: str
    port: int
    user: str
    password: str
    timeout: float


class RPCClient:
    def __init__(self, cfg: RPCConfig, path: str = "/"):
        self._cfg = cfg
        self._path = path

    def call(self, method: str, params: Optional[list[Any]] = None) -> Any:
        payload = json.dumps(
            {"jsonrpc": "1.0", "id": "gbt-miner", "method": method, "params": params or []}
        ).encode("utf-8")
        auth = base64.b64encode(f"{self._cfg.user}:{self._cfg.password}".encode()).decode()
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Basic {auth}",
            "User-Agent": "gbt-miner/0.1",
        }
        conn = http.client.HTTPConnection(self._cfg.host, self._cfg.port, timeout=self._cfg.timeout)
        try:
            conn.request("POST", self._path, body=payload, headers=headers)
            resp = conn.getresponse()
            body = resp.read()
        finally:
            conn.close()

        # Bitcoin Core uses HTTP 500 for JSON-RPC errors. Always parse the body first.
        try:
            decoded = json.loads(body.decode("utf-8"))
        except Exception as e:
            raise RPCError(f"HTTP {resp.status}: failed to parse JSON ({e}): {body[:200]!r}")

        err = decoded.get("error")
        if err:
            raise RPCError(err.get("message", "RPC error"), err.get("code"))
        if resp.status != 200:
            raise RPCError(f"HTTP {resp.status}: {body[:200]!r}")
        return decoded["result"]


def ensure_wallet(wallet_name: str, rpc: RPCClient) -> RPCClient:
    wallet_path = f"/wallet/{wallet_name}"
    wallet_rpc = RPCClient(rpc._cfg, path=wallet_path)
    # If already loaded, done.
    try:
        loaded = rpc.call("listwallets")
        if wallet_name in loaded:
            wallet_rpc.call("getwalletinfo")
            return wallet_rpc
    except RPCError:
        # Wallet RPC may be disabled at compile time; let callers fail later.
        pass

    # Determine if wallet exists on disk.
    wallet_exists = False
    try:
        walletdir = rpc.call("listwalletdir")
        for w in walletdir.get("wallets", []):
            if w.get("name") == wallet_name:
                wallet_exists = True
                break
    except RPCError:
        # If listwalletdir is unavailable, fall back to createwallet below.
        wallet_exists = False

    if wallet_exists:
        rpc.call("loadwallet", [wallet_name])
    else:
        rpc.call(
            "createwallet",
            [
                wallet_name,
                False,  # disable_private_keys
                False,  # blank
                "",  # passphrase
                False,  # avoid_reuse
                True,  # descriptors
                True,  # load_on_startup
            ],
        )

    wallet_rpc.call("getwalletinfo")
    return wallet_rpc


def pick_payout_script(
    *,
    base_rpc: RPCClient,
    wallet_rpc: RPCClient,
    address: Optional[str],
) -> tuple[str, bytes]:
    if address:
        info = base_rpc.call("validateaddress", [address])
        if not info.get("isvalid"):
            raise RuntimeError(f"--address is invalid: {address}")
        spk = bytes.fromhex(info["scriptPubKey"])
        print(f"[miner] Using provided address: {address}", flush=True)
        print(f"[miner] scriptPubKey: {info['scriptPubKey']}", flush=True)
        return address, spk

    addr = wallet_rpc.call("getnewaddress", ["mining", "bech32"])
    info = base_rpc.call("validateaddress", [addr])
    spk = bytes.fromhex(info["scriptPubKey"])
    print("[miner] No --address provided; created a new address via getnewaddress", flush=True)
    print(f"[miner] address: {addr}", flush=True)
    print(f"[miner] scriptPubKey: {info['scriptPubKey']}", flush=True)
    return addr, spk


def build_coinbase_tx(
    *,
    height: int,
    coinbase_value: int,
    payout_script: bytes,
    extranonce: bytes,
    witness_commitment_script: Optional[bytes],
) -> tuple[bytes, bytes]:
    version = 2

    # Must start with CScript() << height << OP_0 (matches Core ContextualCheckBlock).
    script_sig = encode_script_int64(height) + b"\x00" + script_push(extranonce)

    vin = (
        b"\x00" * 32
        + struct.pack("<I", 0xFFFFFFFF)
        + varint(len(script_sig))
        + script_sig
        + struct.pack("<I", 0xFFFFFFFF)
    )

    vout_items: list[bytes] = [
        struct.pack("<Q", coinbase_value) + varint(len(payout_script)) + payout_script
    ]
    if witness_commitment_script:
        vout_items.append(
            struct.pack("<Q", 0)
            + varint(len(witness_commitment_script))
            + witness_commitment_script
        )

    vout = varint(len(vout_items)) + b"".join(vout_items)
    locktime = 0

    # Witness section serializes per-input stacks (no extra count).
    # One input; one stack item; 32-byte reserved value.
    witness = varint(1) + varint(32) + (b"\x00" * 32)

    tx_witness = (
        struct.pack("<I", version)
        + b"\x00\x01"
        + varint(1)
        + vin
        + vout
        + witness
        + struct.pack("<I", locktime)
    )
    tx_nowitness = (
        struct.pack("<I", version)
        + varint(1)
        + vin
        + vout
        + struct.pack("<I", locktime)
    )
    txid_le = sha256d(tx_nowitness)
    return tx_witness, txid_le


def build_block(
    *,
    version: int,
    prevhash_hex: str,
    merkle_root_le: bytes,
    ntime: int,
    nbits_hex: str,
    nonce: int,
    txs: list[bytes],
) -> bytes:
    header = (
        struct.pack("<I", version)
        + ser_uint256_le_from_hex_be(prevhash_hex)
        + merkle_root_le
        + struct.pack("<I", ntime)
        + struct.pack("<I", int(nbits_hex, 16))
        + struct.pack("<I", nonce)
    )
    return header + varint(len(txs)) + b"".join(txs)


def mine_forever(args: argparse.Namespace) -> None:
    cfg = RPCConfig(
        host=args.rpchost,
        port=args.rpcport,
        user=args.rpcuser,
        password=args.rpcpassword,
        timeout=args.rpctimeout,
    )
    base_rpc = RPCClient(cfg, path="/")
    wallet_rpc = ensure_wallet(args.wallet, base_rpc)

    payout_addr, payout_spk = pick_payout_script(
        base_rpc=base_rpc, wallet_rpc=wallet_rpc, address=args.address
    )

    print(f"[miner] RPC endpoint: http://{cfg.host}:{cfg.port}", flush=True)
    print(f"[miner] Wallet: {args.wallet}", flush=True)
    print(f"[miner] Mining payout: {payout_addr}", flush=True)

    blocks_found = 0
    last_prev = None

    while True:
        tmpl = base_rpc.call("getblocktemplate", [{"rules": ["segwit"]}])

        prev = tmpl["previousblockhash"]
        height = int(tmpl["height"])
        version = int(tmpl["version"])
        coinbase_value = int(tmpl["coinbasevalue"])
        nbits_hex = tmpl["bits"]
        nbits = int(nbits_hex, 16)
        target = compact_to_target(nbits)
        mintime = int(tmpl.get("mintime", 0))
        ntime = max(int(tmpl["curtime"]), now(), mintime)

        witness_commitment_hex = tmpl.get("default_witness_commitment", "")
        witness_commitment_script = (
            bytes.fromhex(witness_commitment_hex) if witness_commitment_hex else None
        )

        if prev != last_prev:
            print(
                f"[miner] New template: height={height} prev={prev[:16]}.. bits={nbits_hex} coinbase={coinbase_value}",
                flush=True,
            )
            last_prev = prev

        txs: list[bytes] = []
        txids_le: list[bytes] = []
        for tx in tmpl.get("transactions", []):
            txs.append(bytes.fromhex(tx["data"]))
            txids_le.append(ser_uint256_le_from_hex_be(tx["txid"]))

        extranonce_prefix = struct.pack("<I", os.getpid()) + struct.pack(
            "<I", random.getrandbits(32)
        )
        extranonce_counter = 0
        refetch_template = False

        while True:
            extranonce = extranonce_prefix + struct.pack("<I", extranonce_counter)
            coinbase_tx, coinbase_txid_le = build_coinbase_tx(
                height=height,
                coinbase_value=coinbase_value,
                payout_script=payout_spk,
                extranonce=extranonce,
                witness_commitment_script=witness_commitment_script,
            )

            all_txs = [coinbase_tx] + txs
            all_txids_le = [coinbase_txid_le] + txids_le
            mr_le = merkle_root_le(all_txids_le)

            start_nonce = random.getrandbits(32)
            nonce = start_nonce
            checked = 0
            t0 = time.time()

            while True:
                header = (
                    struct.pack("<I", version)
                    + ser_uint256_le_from_hex_be(prev)
                    + mr_le
                    + struct.pack("<I", ntime)
                    + struct.pack("<I", nbits)
                    + struct.pack("<I", nonce)
                )
                h_be_hex = sha256d(header)[::-1].hex()
                if int(h_be_hex, 16) <= target:
                    block = build_block(
                        version=version,
                        prevhash_hex=prev,
                        merkle_root_le=mr_le,
                        ntime=ntime,
                        nbits_hex=nbits_hex,
                        nonce=nonce,
                        txs=all_txs,
                    )
                    block_hex = block.hex()
                    print(
                        f"[miner] FOUND block hash={h_be_hex} nonce={nonce} extranonce={extranonce_counter}",
                        flush=True,
                    )

                    res = base_rpc.call("submitblock", [block_hex])
                    accepted_primary = res is None
                    if accepted_primary:
                        print("[miner] submitblock: accepted (primary)", flush=True)
                    else:
                        print(f"[miner] submitblock (primary) returned: {res}", flush=True)

                    for submit_ep in args.submit_to:
                        host, port_s = submit_ep.rsplit(":", 1)
                        submit_cfg = RPCConfig(
                            host=host,
                            port=int(port_s),
                            user=args.rpcuser,
                            password=args.rpcpassword,
                            timeout=args.rpctimeout,
                        )
                        submit_rpc = RPCClient(submit_cfg, path="/")
                        try:
                            r2 = submit_rpc.call("submitblock", [block_hex])
                            if r2 is None:
                                print(f"[miner] submitblock: accepted ({submit_ep})", flush=True)
                            else:
                                print(f"[miner] submitblock ({submit_ep}) returned: {r2}", flush=True)
                        except Exception as e:
                            print(f"[miner] submitblock failed on {submit_ep}: {e}", flush=True)

                    if accepted_primary:
                        blocks_found += 1
                        if args.max_blocks and blocks_found >= args.max_blocks:
                            print(f"[miner] Reached --max-blocks={args.max_blocks}; exiting", flush=True)
                            return
                    refetch_template = True
                    break

                nonce = (nonce + 1) & 0xFFFFFFFF
                checked += 1

                if checked % args.status_every == 0:
                    dt = max(time.time() - t0, 1e-6)
                    hps = int(checked / dt)
                    print(
                        f"[miner] hashing ~{hps}/s (height={height} nonce={nonce} extranonce={extranonce_counter})",
                        flush=True,
                    )

                if checked % args.refresh_every == 0:
                    ntime = max(ntime, now(), mintime)
                    try:
                        best = base_rpc.call("getbestblockhash")
                        if best != prev:
                            print("[miner] Tip changed; discarding stale work", flush=True)
                            refetch_template = True
                            break
                    except Exception:
                        pass

            if refetch_template:
                break

            extranonce_counter += 1
            if extranonce_counter > args.max_extranonce:
                print("[miner] Extranonce rollover; refetching template", flush=True)
                break


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="GBT solo miner (getblocktemplate + submitblock)")
    p.add_argument("--rpchost", default="127.0.0.1")
    p.add_argument(
        "--rpcport", type=int, default=28476, help="RPC port for testNodes2 (default: 28476)"
    )
    p.add_argument("--rpcuser", default="user")
    p.add_argument("--rpcpassword", default="pass")
    p.add_argument("--rpctimeout", type=float, default=10.0)
    p.add_argument("--wallet", default="miner", help="Wallet name to create/load if needed")

    p.add_argument(
        "--address",
        default=None,
        help="Payout address. If omitted, script calls getnewaddress and logs the generated address.",
    )
    p.add_argument(
        "--submit-to",
        action="append",
        default=[],
        help="Optional extra node RPC endpoints host:port to also submit found blocks to (repeatable).",
    )

    p.add_argument("--max-blocks", type=int, default=0, help="Stop after N accepted blocks (0 = infinite)")
    p.add_argument("--status-every", type=int, default=200000, help="Print hashrate every N headers checked")
    p.add_argument("--refresh-every", type=int, default=500000, help="Refresh time / check tip every N headers")
    p.add_argument("--max-extranonce", type=int, default=5000, help="Max extranonce attempts per template")
    return p.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    args.max_blocks = int(args.max_blocks) if args.max_blocks else 0
    try:
        mine_forever(args)
    except KeyboardInterrupt:
        print("\n[miner] interrupted", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
