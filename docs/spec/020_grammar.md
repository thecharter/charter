# 020 — Grammar

**Status:** draft (2026-11-06). Deterministic recursive-descent grammar of the unified Charter language (`src/Charter/Surface/{Lexer,Parser}.lean`, `D2`, `D14`, `D17`), verified against `docs/spec/` by `test/gates/spec-inventory.sh` and round-trip tested by `charter fmt` (`test/spec/spec_018_4_fmt_roundtrip.charter`).

---

## 20.1 Lexical classes (`002`)

```ebnf
ident       ::= lower (lower | '_' | '-' lower)* (' '+ lower (lower | '_' | '-' lower)*)*
              | '[' (any-char-except ']' '>' '+' '=' '\n')* ']'
atom        ::= upper (alpha | digit | '_')*          (* excluding reserved wordKeywords *)
int_lit     ::= digit+
str_lit     ::= '"' (escape | char)* '"'
char_lit    ::= "'" alphanum "'"
proj_dot    ::= '.'                                   (* glued left, followed by lower | '(' | '[' *)
var         ::= ident int_lit? "'"*
clause_id   ::= (atom | ident | int_lit) ('.' (atom | ident | int_lit))*
```

Reserved multi-word and word keywords (`wordKeywords`):
`Derived externally`, `Conditioned by`, `Identified by`, `Terminated by`, `Violated when`, `Overridden by`, `Present when`, `Current Time`, `Derived from`, `Except under`, `Enforced by`, `Related to`, `Syncs with`, `Valid when`, `Created by`, `Due within`, `Holds when`, `Placeholder`, `Obfuscates`, `Terminates`, `Identified`, `Recipient`, `Invariant`, `Predicate`, `Physical`, `Claimant`, `Function`, `Violated`, `Enabled`, `Creates`, `Current`, `Derived`, `Present`, `Foreach`, `Exists`, `Forall`, `Extend`, `Closed`, `Domain`, `Holder`, `String`, `Actor`, `Count`, `Event`, `False`, `Force`, `Holds`, `Union`, `Where`, `Atom`, `Bool`, `Duty`, `Fact`, `Open`, `Time`, `True`, `When`, `With`, `Act`, `For`, `Int`, `Max`, `Min`, `Not`, `Sum`, `Var`, `Do`.

Claim keywords (matched when followed by whitespace and a non-`.`/`}` token):
`?!violated`, `?!lawful`, `?!valid`, `?violated`, `?lawful`, `?valid`, `?why`.

Contextual keywords (`D17`, lexed as `atom` or `ident` and matched only in the grammar positions below):
`Document`, `Clause`, `Approved`, `Text`, `Norm`, `Definition`, `Acceptance`, `Commentary`, `From`, `Immunity`, `Against`, `Unless`, `Duration`, `Held`, `Param`, `Module`, `Use`, `As`, `Scenario`, `tick`.

---

## 20.2 Top-level items and phrases (`011`)

```ebnf
file        ::= item* EOF

item        ::= directive '.'
              | '{' par_phrases '}'
              | 'Scenario' (ident | atom | str_lit) from_clause* '{' scen_phrases '}'
              | phrase ('.' | EOF)

directive   ::= '#include' str_lit
              | '#require' str_lit

par_phrases ::= /* empty */
              | phrase ('.' par_phrases | '}')

scen_phrases ::= /* empty */
               | '{' par_phrases '}' scen_phrases
               | phrase ('.' scen_phrases | '}')

phrase      ::= frame+
              | '+' opt_foreach
              | '-' opt_foreach
              | '~' opt_foreach
              | '?' expr
              | '!?' expr
              | '?-' opt_foreach
              | '?--' opt_foreach
              | ('?lawful' | '?valid' | '?violated' | '?!lawful' | '?!valid' | '?!violated') expr
              | '?why' expr
              | '@' expr
              | 'tick'                                (* before '.', '}', or EOF *)
              | '!'? opt_foreach

opt_foreach ::= '(' 'Foreach' vars ':' expr ')'
              | expr
```

---

## 20.3 Declarations and clauses (`003`–`009`, `012`–`015`)

```ebnf
frame       ::= ('Open' | 'Closed')? frame_body

frame_body  ::= ('Fact' | 'Var' | 'Function') ident ('Identified by' domain)? dom_filter? fact_clause*
              | 'Bool' ident fact_clause*
              | ('Predicate' | 'Invariant') ident ('When' | 'Where') expr from_clause*
              | 'Act' ident 'With'? ('Actor' var)? ('Recipient' var)? ('Related to' vars)? dom_filter? act_clause*
              | 'Physical' ident 'With'? ('Actor' var)? ('Related to' vars)? dom_filter? act_clause*
              | 'Event' ident 'With'? ('Related to' vars)? dom_filter? event_clause*
              | 'Duty' ident 'With'? 'Holder' var 'Claimant' var ('Related to' vars)? dom_filter? duty_clause*
              | 'Immunity' ident 'With'? 'Holder' var ('Related to' vars)? dom_filter? immunity_clause*
              | 'Extend' ('Fact' ident fact_clause*
                        | 'Act' ident act_clause*
                        | 'Event' ident event_clause*
                        | 'Duty' ident duty_clause*
                        | 'Immunity' ident immunity_clause*)
              | 'Placeholder' ident 'For' ident
              | 'Module' ident '(' idents? ')' '{' (frame | '.')* '}'
              | 'Use' ident '(' idents? ')' ('As' ident)?
              | 'Param' ident (':' ('Int' | 'Time' | 'Duration'))? '=' '-'? int_lit
              | 'Document' str_lit
              | 'Clause' clause_id ('Approved' int_lit)? clause_item*

dom_filter  ::= ('When' | 'Where') expr
from_clause ::= 'From' clause_id str_lit

clause_item ::= 'Text' str_lit
              | ('Norm' | 'Definition' | 'Invariant' | 'Acceptance' | 'Commentary') str_lit ('=>' idents)?

domain      ::= 'String' | 'Atom' | 'Int' | 'Time' | 'Duration'
              | int_lit ('..' int_lit | ((',' | '+') int_lit)*)
              | char_lit '..' char_lit
              | (atom | str_lit) ((',' | '+') (atom | str_lit))*
              | '(' var ('*' var)* ')'
              | var ('*' var)*

deriv_clause ::= 'Derived from' opt_foreach (',' opt_foreach)*
               | ('Holds when' | 'Present when' | 'Holds' 'When' | 'Present' 'When') expr_list

fact_clause     ::= 'Conditioned by' expr_list? | 'Open' | 'Closed'
                  | ('Identified by' | 'Domain') ext_domain | from_clause | deriv_clause
act_clause      ::= 'Conditioned by' expr_list? | 'Open' | 'Closed'
                  | 'Creates' create_eff (',' create_eff)*
                  | 'Terminates' opt_foreach (',' opt_foreach)*
                  | 'Obfuscates' opt_foreach (',' opt_foreach)*
                  | 'Syncs with' opt_foreach (',' opt_foreach)*
                  | 'Valid when' expr_list | 'Except under' idents
                  | from_clause | deriv_clause
event_clause    ::= 'Conditioned by' expr_list? | 'Open' | 'Closed'
                  | 'Creates' create_eff (',' create_eff)*
                  | 'Terminates' opt_foreach (',' opt_foreach)*
                  | 'Obfuscates' opt_foreach (',' opt_foreach)*
                  | 'Syncs with' opt_foreach (',' opt_foreach)*
                  | deriv_clause
duty_clause     ::= 'Conditioned by' expr_list? | 'Open' | 'Closed'
                  | 'Violated when' expr_list | 'Enforced by' idents
                  | 'Terminated by' idents | 'Created by' idents
                  | 'Overridden by' idents | 'Due within' expr
                  | from_clause | deriv_clause
immunity_clause ::= 'Conditioned by' expr_list? | 'Open' | 'Closed'
                  | 'Against' idents | 'Unless' expr_list
                  | from_clause | deriv_clause

create_eff  ::= opt_foreach ('For' expr)?
```

---

## 20.4 Expressions and precedence (`010`, lowest to highest)

```ebnf
expr        ::= or_expr (('When' | 'Where') or_expr)*            (* left-assoc, D14 *)
or_expr     ::= and_expr ('||' and_expr)*                        (* left-assoc *)
and_expr    ::= cmp_expr ('&&' cmp_expr)*                        (* left-assoc *)
cmp_expr    ::= add_expr (('==' | '!=' | '<=' | '>=' | '<' | '>') add_expr)?
add_expr    ::= mul_expr (('+' | '-') mul_expr)*                 (* left-assoc *)
mul_expr    ::= unary_expr (('*' | '/' | '%') unary_expr)*       (* left-assoc *)
unary_expr  ::= ('!' | 'Not' | 'Present' | 'Holds' | 'Violated' | 'Enabled') unary_expr
              | 'Held' '(' expr ')' 'For' add_expr
              | postfix_expr
postfix_expr ::= primary (proj_dot (var | '(' var ')') | ':' ident)*
primary     ::= 'True' | 'False' | 'Current Time'
              | int_lit | str_lit | atom
              | ('Sum' | 'Count' | 'Max' | 'Min') '(' 'Foreach' vars ':' expr ')'
              | '(' 'Exists' vars ':' expr ')'
              | '(' 'Forall' vars ':' expr ')'
              | '(' expr ')'
              | ident '(' args ')'
              | var
args        ::= /* empty */
              | var '=' expr (',' var '=' expr)*
              | expr (',' expr)*
```
