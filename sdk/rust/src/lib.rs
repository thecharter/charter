//! Typed Rust SDK models & request builders for operator-blind `charter-server` (`sdk/openapi.json`, G5.4).

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarArg {
    Str(String),
    Int(i64),
}

impl ScalarArg {
    pub fn to_json(&self) -> String {
        match self {
            ScalarArg::Str(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
            ScalarArg::Int(n) => n.to_string(),
        }
    }
}

pub fn build_evaluate_request(institution_id: &str, action: &str, args: &[ScalarArg]) -> String {
    let args_json: Vec<String> = args.iter().map(ScalarArg::to_json).collect();
    format!(
        "{{\"op\":\"Evaluate\",\"institutionId\":\"{}\",\"action\":\"{}\",\"args\":[{}]}}",
        institution_id,
        action,
        args_json.join(",")
    )
}

pub fn build_reserve_request(
    institution_id: &str,
    intent_id: &str,
    actor: &str,
    action: &str,
    args: &[ScalarArg],
    resource: &str,
    amount: i64,
    ttl: i64,
) -> String {
    let args_json: Vec<String> = args.iter().map(ScalarArg::to_json).collect();
    format!(
        "{{\"op\":\"Reserve\",\"institutionId\":\"{}\",\"intentId\":\"{}\",\"actor\":\"{}\",\"action\":\"{}\",\"args\":[{}],\"resource\":\"{}\",\"amount\":{},\"ttl\":{}}}",
        institution_id,
        intent_id,
        actor,
        action,
        args_json.join(","),
        resource,
        amount,
        ttl
    )
}
