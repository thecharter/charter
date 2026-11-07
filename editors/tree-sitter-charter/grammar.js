// Tree-sitter grammar for Charter 1.0 (unified stratified-eFLINT 4.1 superset, spec 020)
module.exports = grammar({
  name: 'charter',
  extras: $ => [/\s/, $.line_comment, $.block_comment],
  rules: {
    source_file: $ => repeat($._item),
    _item: $ => choice($.directive, $.scenario, $.phrase),
    line_comment: _ => token(seq('//', /.*/)),
    block_comment: _ => token(seq('/*', /[^*]*\*+([^/*][^*]*\*+)*/, '/')),
    directive: $ => seq(choice('#include', '#require'), $.string_lit, '.'),
    scenario: $ => seq('Scenario', choice($.ident, $.atom, $.string_lit), '{', repeat($.phrase), '}'),
    phrase: $ => seq(choice($.declaration, $.claim_phrase, $.action_phrase), optional('.')),
    declaration: $ => seq(
      optional(choice('Open', 'Closed', 'Evidenced', 'Entrenched')),
      choice('Fact', 'Var', 'Function', 'Bool', 'Act', 'Power', 'Finding', 'Amend',
             'Physical', 'Event', 'Duty', 'Immunity', 'Invariant', 'Predicate',
             'Property', 'Param', 'Regime', 'Module', 'Use', 'Document', 'Clause', 'Extend', 'Placeholder'),
      repeat($._token_any)
    ),
    claim_phrase: $ => seq(
      choice('?', '!?', '?lawful', '?valid', '?violated', '?undetermined', '?conflict',
             '?!lawful', '?!valid', '?!violated', '?!undetermined', '?!conflict', '?why'),
      repeat1($._token_any)
    ),
    action_phrase: $ => seq(optional(choice('+', '-', '~', '@')), repeat1($._token_any)),
    _token_any: $ => choice($.ident, $.atom, $.int_lit, $.string_lit, '(', ')', ',', '*', ':', '=', '&&', '||', '==', '!=', '<=', '>='),
    ident: _ => /[a-z_][a-z0-9_-]*/,
    atom: _ => /[A-Z][A-Za-z0-9_]*/,
    int_lit: _ => /[0-9]+/,
    string_lit: _ => /"([^"\\]|\\.)*"/
  }
});
