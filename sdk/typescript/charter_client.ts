// Typed TypeScript SDK for operator-blind `charter-server` (`sdk/openapi.json`, G5.4)

export type ScalarArg = string | number;
export type DecisionOutcome =
  | "Allow"
  | "Deny"
  | "NeedEvidence"
  | "ReferForFinding"
  | "Conflict"
  | "Observed"
  | "Reserved";
export type TriStatus = "yes" | "no" | "undetermined";

export interface AuthorizationToken {
  institutionId: string;
  lawHash: string;
  stateVersion: number;
  reservationId: string;
  intentId: string;
  actor: string;
  action: string;
  argsDigest: string;
  maxAmount: number;
  nonce: string;
  expiresAt: number;
  signatureHex: string;
}

export interface ServerResponse {
  ok: boolean;
  op: string;
  institutionId: string;
  lawHash: string;
  lawVersion?: number;
  stateVersion: number;
  stateRoot?: string;
  outcome?: DecisionOutcome;
  lawful?: TriStatus;
  valid?: TriStatus;
  token?: AuthorizationToken;
  sagaStatus?: string;
  error?: string;
}

export interface Transport {
  send(requestJson: string): Promise<string>;
}

export class CharterClient {
  constructor(
    private readonly transport: Transport,
    private readonly institutionId: string = "default-institution"
  ) {}

  async request(payload: Record<string, unknown>): Promise<ServerResponse> {
    const raw = await this.transport.send(
      JSON.stringify({ institutionId: this.institutionId, ...payload })
    );
    return JSON.parse(raw) as ServerResponse;
  }

  evaluate(action: string, args: ScalarArg[]): Promise<ServerResponse> {
    return this.request({ op: "Evaluate", action, args });
  }

  reserve(params: {
    intentId: string;
    actor: string;
    action: string;
    args: ScalarArg[];
    resource?: string;
    amount?: number;
    resourceCap?: number;
    ttl?: number;
  }): Promise<ServerResponse> {
    return this.request({ op: "Reserve", ...params });
  }

  authorize(intentId: string): Promise<ServerResponse> {
    return this.request({ op: "Authorize", intentId });
  }

  confirmExecution(
    token: AuthorizationToken,
    status: "confirmed" | "timeout_unknown" = "confirmed",
    receiptRef?: string
  ): Promise<ServerResponse> {
    return this.request({ op: "ConfirmExecution", token, status, receiptRef });
  }
}
