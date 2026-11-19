---
title: "On eFLINT, Charter, and the Foundations of\\newline an Executable Institutional Economy"
subtitle: "An open letter to L. Thomas van Binsbergen"
date: "10 November 2026"
geometry: "margin=1.0in"
fontsize: 11pt
mainfont: "Palatino"
monofont: "Menlo"
monofontoptions: "Scale=0.78"
linestretch: 1.06
colorlinks: true
linkcolor: "black"
urlcolor: "blue!50!black"
header-includes:
  - \usepackage{titling}
  - \setlength{\droptitle}{-4em}
  - \pretitle{\begin{flushleft}\Large\bfseries}
  - \posttitle{\par\end{flushleft}}
  - \preauthor{}
  - \postauthor{}
  - \predate{\begin{flushleft}}
  - \postdate{\par\end{flushleft}\vspace{-1em}}
  - \usepackage{enumitem}
  - \setlist{itemsep=2pt,topsep=4pt}
  - \usepackage{needspace}
  - \widowpenalty=10000
  - \clubpenalty=10000
  - \emergencystretch=1.5em
  - \pagestyle{plain}
---

Dear Dr. van Binsbergen,

I am writing to you about Charter, a language for specifying and verifying institutions that I began independently, and that now rests on eFLINT's semantic foundations. When I encountered eFLINT after much of Charter's conceptual design was already in place, I recognized that you and your collaborators had already given computational form to ideas I had been working toward from another angle. Rather than maintain a separate foundation for concepts we understood in much the same way, I rebased Charter onto eFLINT.

Reading your [GPCE 2020 paper](https://doi.org/10.1145/3425898.3426958) alongside your [recent reflections](https://doi.org/10.1016/j.cola.2026.101411) in the *Journal of Computer Languages* and your [*JustAct* article](https://doi.org/10.46298/lmcs-22(3:9)2026) in *Logical Methods in Computer Science* with Christopher A. Esterhuyse and Tim Müller deepened my respect for that body of work. Together they trace a remarkable arc: from an executable calculus of normative relations, through an unusually candid reckoning with its language-design trade-offs, to federated coordination among agents that share neither a global view of state nor the contents of their private policies. Yet I came away—especially from the reflections paper—with the impression that your modesty gives far more weight to what remains unfinished than to the significance of what you have already accomplished. I wanted to offer the perspective of someone who arrived at the same territory by a different route.

## What I believe you discovered

I regard eFLINT as a foundational advance in computing—not because every choice in its semantics is final or because it resolves the human difficulty of legal interpretation, which no formalism can, but because it gives executable form to something computing has largely lacked: the institutional relationships that determine what actions mean, who holds authority to perform them, what obligations they create, and how those relationships change over time.

Software already has languages for computation, databases for facts, protocols for communication, and access-control mechanisms for deciding which operations a system will permit. Institutions are something else. An institution can impose an obligation without guaranteeing its fulfillment. It can confer power to alter another party's legal position. It can recognize an improper act as legally consequential, hold one party accountable to another, and establish procedures through which its own rules are amended. These are not access-control checks or collections of business rules; they form a distinct computational domain. By joining Hohfeldian legal relations to an executable transition semantics, eFLINT turns rights, duties, and powers from informal commentary around a program into first-class objects a system can represent, execute, inspect, and reason about.

The importance of that step reaches well beyond regulatory compliance, valuable as compliance is. An increasingly autonomous economy will require software agents, organizations, and people to transact across systems none of them unilaterally controls. Those participants will need shared ways to establish authority, recognize obligations, determine whether purported acts took effect, resolve disputes, and account for remedies. Today, most of that institutional machinery either remains outside software—in legal prose, organizational procedures, and human administration—or gets reinvented piecemeal inside application code.

That arrangement will not scale to an economy of autonomous actors. Such an economy requires not merely programmable transactions, but *programmable institutions*: shared, inspectable, and enforceable accounts of the relationships under which transactions carry authority and obligation. Whether the mature medium for this turns out to be eFLINT itself or a descendant that looks quite different, you recognized unusually early that the institutional layer could become a computational object in its own right, independent of any particular application governed by it.

## Converging from another direction

My own path into this problem began not with compliance monitoring, but with self-governing institutions: constitutions, multi-party protocols, and organizations that must constrain and amend their own authority over time. To represent them faithfully, I needed to distinguish an event occurring from its being lawful, and both from its producing a valid institutional effect. I needed authority that could be delegated, bounded, or entrenched against ordinary amendment, and procedures through which contested external facts could be weighed and settled by institutional findings.

Those pressures led me toward a vocabulary of facts, acts, duties, powers, and evolving normative state before I knew eFLINT existed. Independent convergence does not prove a formalism inevitable, any more than two travelers taking the same mountain pass prove there is no other way across. Still, arriving at the same structure from constitutional governance rather than regulatory compliance suggested to me that the abstraction captures something real in the shape of institutions themselves, rather than the habits of a single research program.

For that reason, I built Charter as a syntactic and semantic superset of well-stratified eFLINT rather than borrowing your vocabulary and quietly changing what its constructs mean. Existing eFLINT specifications whose derivations stratify and whose type extensions are written explicitly run directly in Charter without a compatibility mode, and Charter's additions operate as extensions of that foundation rather than replacements for it. Preserving compatibility has been a salutary discipline: testing continuously against eFLINT's own examples and test suite has forced me to distinguish genuinely new institutional concepts from mere preferences about things eFLINT already expresses well. Where Charter does diverge—principally in rejecting self-negating derivations that cannot be stratified, alongside a small number of edge cases involving derivation order, type redeclaration, and operator precedence—I have documented each case in reproducible detail and would gladly contribute reports upstream where useful, especially where behavior that looks anomalous from a least-fixpoint standpoint may reflect an intended idiom.

## Where our designs have taken different directions

Charter's central addition to eFLINT's model is the separation of *occurrence*, *lawfulness*, and *validity*. In your papers you explain why a disabled action must remain capable of occurring and producing consequences: a normative system has to describe violations and their aftermath, not pretend forbidden acts are impossible. I agree completely. Yet self-governing institutions also require a distinction between performing an act and successfully exercising the legal power that act purports to exercise. A board can call a vote without a quorum; an officer can issue an order beyond the scope of the office; a legislature can pass an amendment that collides with an entrenched constitutional protection. In each case the attempt occurs, and it may constitute a violation, but it does not bring about the institutional change its author intended.

Charter therefore introduces `Valid when` alongside permission, determining whether an action's institutional effects take hold independently of whether the action was lawful, while preserving eFLINT's behavior when omitted. Paired with explicit Hohfeldian immunities—through which an actor or rule is protected against specified exercises of another's power—this makes it possible to model not only institutional action, but the boundaries of institutional competence.

Other extensions grew out of watching institutions operate across disagreement and uncertainty. Rather than encoding defaults through negated derivations or evaluation order, Charter expresses defaults, exceptions, and priorities directly, surfacing unresolved conflicts when rules of equal standing disagree. In much the same spirit, it separates evidence about external facts—which may be absent, unresolved, or contradictory—from authoritative institutional findings that settle a disputed question under a declared standard.

Institutions also live in time and answer to governing texts. Charter represents clocks, expiring entitlements, and deadlines natively while retaining external qualification for open-textured standards such as "undue delay," and it binds formal rules to verbatim passages of their governing prose documents so that edits to an authoritative text immediately flag interpretations whose recorded approval has gone stale. Throughout, eFLINT's original constructs remain the substrate on which these additions rest.

## Why Lean 4

I implemented Charter in Lean 4 because I wanted a language whose execution could itself be subjected to formal proof. In an ordinary application, an interpreter defect produces an incorrect calculation or an unexpected program state. In an executable institution, an interpreter defect could silently confer ungranted authority, extinguish an obligation, recognize an *ultra vires* act, or allow a protected rule to be amended away. If software is to administer institutional authority, confidence in its semantics becomes part of the institution's trustworthiness.

Lean makes it possible to write Charter's live evaluator in the same formal setting in which theorems about its behavior are stated and machine-checked, rather than formalizing an outer protocol around an axiomatized evaluator or maintaining a separate paper model alongside an unverified interpreter. Correspondence between the live evaluator and an independent relational semantics, determinism of execution, preservation of unaffected state, least-fixpoint behavior of stratified derivation, and preservation of entrenched protections across authorized amendments are proved directly over the implementation. Beyond general metatheory, Charter can also ask Lean's small trusted kernel to certify both concrete institutional executions and inductive invariants of a specification itself.

Formal verification has plain limits: a proof kernel cannot establish that a formal rule faithfully captures the human meaning of a legal text, nor can it vouch for external inputs or the surrounding runtime environment. What it offers is a way to narrow and make explicit what participants must take on trust. Just as importantly, Lean stays beneath the surface. An author specifying an institution should work in the language of powers, duties, immunities, evidence, and amendments—never in the language of proof assistants. That is another reason eFLINT proved such a compelling starting point: its concepts already offered the institutional vocabulary I needed, and Lean offered a way to place machine-checked guarantees underneath it.

## What I take from your reflections and from *JustAct*

I read your reflections paper not as a specification to satisfy, but as field notes from someone who confronted related tensions earlier. I was especially struck by your observation that flexibility is not always an advantage, and that particular applications often depend on guarantees only a more restrictive language can enforce. Choosing stratified derivation, explicit institutional validity, and stricter static checks in Charter excluded certain concise programs, yet each restriction bought back predictability, explainability, or amenability to verification. Your discussion of concrete versus symbolic knowledge, finite versus open domains, the interplay of declarative and procedural reasoning, and your experiments compiling eFLINT toward Solidity all touch trade-offs Charter is encountering firsthand in verification and target projection.

I am similarly intrigued by the contrasting choices you have explored around surface languages and composition. Facing the tension between legal readability and operational machinery such as `Syncs with`, I kept a single typed, stratified language that elaborates into an inspectable internal core, so that the powers, duties, and protections written by an author remain the exact objects traced through execution, explanation, verification, and amendment. Seeing how Slick moves in almost the opposite direction inside *JustAct*—adopting untyped, natural-language-like rules under three-valued well-founded semantics so independently authored policies can compose safely without central coordination—clarified for me what a separate compositional layer can buy when mutually distrusting peers contribute rules at runtime.

More directly still, reading *JustAct* before sending this letter reshaped both Charter and its original motivating institution, the [Protocol of Sovereign Agency](https://github.com/thecharter/psa). Until then, I had modeled institutional execution primarily along a single coherent timeline. *JustAct* put its finger on an assumption that does not survive contact with inter-organizational life: autonomous parties frequently cannot synchronize every policy change globally, nor can they publish sensitive delegations and commercial terms onto a shared ledger merely to prove that an action was permitted. Your separation of infrequent synchronized agreements from peer-to-peer statements—and the insight that evaluating non-monotonic rules inside a closed, action-carried payload preserves monotone auditability as network history grows—prompted me to extend Charter with action-carried justification bundles proved directly over its live evaluator.

Working through the scenarios and open questions of *JustAct* proved equally generative. Because Charter already carried machine-checked evaluation, stateful obligations, notice-gated deadlines, and audience-scoped confidentiality in Lean, bringing action-carried payloads into Charter made it natural to carry formal verification all the way through policy evaluation without unproved evaluator assumptions, and to pair closed-bundle auditing with standing conditional delegations, per-statement revocation across amended agreements, commitment-backed redaction of confidential premises, audience bounds on statement forwarding, and obligations whose deadlines do not run before notice reaches the obligor. Watching *JustAct*'s candid treatment of unregulated forwarding, partial-view obligations, and emergency agreement updates also exposed concrete gaps in the Protocol of Sovereign Agency itself—leading me to sharpen its rules around standing offline mandates, notice-gated procedural demands, bond slashing for leaked confidential records, and the principle that another party's suspected breach can never justify a blanket freeze across uninvolved agents. It was a pleasure to discover how naturally those pieces fit together once your framing made the missing problems visible.

Above all, I appreciated your candor across these papers that legal interpretation and qualification remain inherently subjective. Executable institutional specifications neither can nor should abolish that subjectivity. What they can do is make an interpretation explicit, trace its consequences, expose its dependencies, and allow competing readings of a text to be compared in the open—which strikes me as a genuine advance precisely because the ultimate judgment remains human.

## The larger possibility

The further I have developed Charter, the more convinced I have become that the distinction between technical capability and institutional authority will matter enormously in the years ahead. Autonomous agents are rapidly becoming capable of negotiating agreements, managing resources, exercising delegated discretion, and coordinating economic activity across organizational boundaries. Yet competence to perform an action is not authority to perform it. A software agent may hold the technical means to move an asset without possessing the institutional power to transfer title; it may fulfill one agreement in a way that violates an overriding duty; it may receive conflicting directives from principals whose relationships cannot be flattened into an access-control hierarchy.

The law is already beginning to test these boundaries. [Wyoming's DAO LLC statute](https://sos.wyo.gov/Business/BusinessStatute.aspx), enacted in 2021, recognized legal entities whose governance may be conducted partly through smart contracts, and Delaware has recently explored a regulatory-sandbox proposal for [Artificial Intelligence Companies](https://www.delawarepublic.org/politics-government/2026-10-30/congressional-oversight-committee-questions-delawares-work-on-artificial-intelligence-companies) under which an autonomous system could manage a legal entity. Neither effort supplies a general semantics of institutional authority, and Delaware's proposal remains exploratory, yet both point toward organizations whose governance cannot rest on prompt instructions or opaque application logic alone. If such entities are to transact reliably among independent parties, they will need shared institutional accounts capable of distinguishing what happened from what was permitted and what took valid effect, explaining those judgments from preserved rules, and holding participants accountable when they act outside them.

A formal specification language is only one piece of that future; questions of jurisdiction, evidentiary truth, adoption, interoperability, and legitimate authority belong to law and society rather than programming-language design. Even so, the computational foundation is indispensable, and eFLINT recognized a remarkably large share of that foundation well before the surrounding need became plain.

\needspace{12\baselineskip}

## An invitation

If this letter reaches you, I would particularly welcome your thoughts on three questions:

1. In eFLINT, whether an action is enabled (`Holds when`) carries both action-compliance and the Hohfeldian power–liability relation, yet a disabled action still produces its post-conditions when executed. Does Charter's separation of permission from `Valid when` and explicit immunities fit naturally within how you view Hohfeldian powers and disabilities today, or would you model ineffective exercises of power differently?
2. Between eFLINT's stateful normative types and Slick's untyped, well-founded rules for peer composition, how has your thinking evolved on the trade-off between static structure and open multi-author composition—and on where legal surface languages should meet computational semantics?
3. *JustAct* gains concurrency and policy privacy by keeping decentralized history grow-only and local to each action's payload, whereas economic institutions also depend on stateful obligations, deadlines, revocable authority, and conservation laws. Where do you think local justification bundles should end and shared institutional state or settlement must begin?

Charter's implementation and compatibility notes live at [github.com/thecharter/charter](https://github.com/thecharter/charter), alongside the [Protocol of Sovereign Agency](https://github.com/thecharter/psa).

I do not view Charter as a successor to eFLINT, nor do I imagine its choices settle the questions your work raises. What I wanted above all to convey is that your work may be more consequential than the modest, self-critical tone of your papers suggests. Beneath the real limitations and open research problems you identify sits an insight that deserves wide recognition: *institutional reality can be given an executable computational form without reducing it to the mechanics of the systems it governs.*

I am grateful that you and your collaborators developed that idea with enough precision, generality, and openness that someone approaching the problem from elsewhere could recognize its value and build upon it.

With respect and appreciation,

**Eric Hartford**  
eric@quixi.ai  
ORCID: [0009-0002-0159-2127](https://orcid.org/0009-0002-0159-2127)  
Google Scholar: [SwrFngsAAAAJ](https://scholar.google.com/citations?user=SwrFngsAAAAJ&hl=en)
