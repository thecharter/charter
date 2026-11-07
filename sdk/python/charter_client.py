"""Typed Python client SDK for operator-blind `charter-server` (`sdk/openapi.json`, G5.4)."""
from __future__ import annotations
import json
import subprocess
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Union

ScalarArg = Union[str, int]


@dataclass
class CharterDecision:
    ok: bool
    op: str
    institution_id: str
    law_hash: str
    state_version: int
    state_root: Optional[str]
    outcome: Optional[str]
    lawful: Optional[str]
    valid: Optional[str]
    raw: Dict[str, Any]


class CharterStdioClient:
    """Persistent stdio JSON-RPC client for a running `charter-server serve` subprocess."""

    def __init__(self, server_bin: str, artifact_path: str, institution_id: str = "default-institution",
                 log_path: Optional[str] = None, key: Optional[str] = None) -> None:
        cmd = [server_bin, "serve", artifact_path, "--institution", institution_id]
        if log_path is not None:
            cmd.extend(["--log", log_path])
        if key is not None:
            cmd.extend(["--key", key])
        self._proc = subprocess.Popen(
            cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        self.institution_id = institution_id

    def call(self, payload: Dict[str, Any]) -> CharterDecision:
        assert self._proc.stdin is not None and self._proc.stdout is not None
        req = dict(payload)
        req.setdefault("institutionId", self.institution_id)
        self._proc.stdin.write(json.dumps(req) + "\n")
        self._proc.stdin.flush()
        line = self._proc.stdout.readline()
        if not line:
            err = self._proc.stderr.read() if self._proc.stderr else ""
            raise RuntimeError(f"charter-server closed stdout unexpectedly: {err}")
        data = json.loads(line)
        return CharterDecision(
            ok=bool(data.get("ok")),
            op=str(data.get("op", "")),
            institution_id=str(data.get("institutionId", "")),
            law_hash=str(data.get("lawHash", "")),
            state_version=int(data.get("stateVersion", 0)),
            state_root=data.get("stateRoot"),
            outcome=data.get("outcome"),
            lawful=data.get("lawful"),
            valid=data.get("valid"),
            raw=data,
        )

    def evaluate(self, action: str, args: List[ScalarArg]) -> CharterDecision:
        return self.call({"op": "Evaluate", "action": action, "args": args})

    def reserve(self, intent_id: str, actor: str, action: str, args: List[ScalarArg],
                resource: str = "", amount: int = 0, resource_cap: Optional[int] = None, ttl: int = 10) -> CharterDecision:
        req: Dict[str, Any] = {
            "op": "Reserve", "intentId": intent_id, "actor": actor, "action": action,
            "args": args, "resource": resource, "amount": amount, "ttl": ttl,
        }
        if resource_cap is not None:
            req["resourceCap"] = resource_cap
        return self.call(req)

    def authorize(self, intent_id: str) -> CharterDecision:
        return self.call({"op": "Authorize", "intentId": intent_id})

    def confirm_execution(self, token: Dict[str, Any], status: str = "confirmed", receipt_ref: Optional[str] = None) -> CharterDecision:
        req: Dict[str, Any] = {"op": "ConfirmExecution", "token": token, "status": status}
        if receipt_ref is not None:
            req["receiptRef"] = receipt_ref
        return self.call(req)

    def explain(self, target: str, args: List[ScalarArg], audience: Optional[str] = None) -> CharterDecision:
        req: Dict[str, Any] = {"op": "Explain", "target": target, "args": args}
        if audience is not None:
            req["audience"] = audience
        return self.call(req)

    def close(self) -> None:
        if self._proc.stdin and not self._proc.stdin.closed:
            self._proc.stdin.close()
        self._proc.wait(timeout=5)
