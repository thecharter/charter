# Homework Policies Benchmark

This project describes a contrived toy-example of simultaneously a (software) system and norms that govern the system. 
The goal is to admit several solutions to expressing the norms as computational artifacts on the one hand and constructing the software system with embedded enforcement mechanisms. 

The example is chosen such that solutions can demonstrate:

* The chosen (formal) representation of normative sources, and its capabilities for reuse, abstraction and specialization
* The combination of norms from a variety of sources, including mechanisms for prioritizing norms in case of conflicts.
* Static ex-ante enforcement mechanisms, ensuring norms are respected by the software system at runtime by applying the norms as part of the software production process (before runtime)
* Dynamic ex-ante enforcement mechanisms, applying the norms at runtime to ensure compliance
* Fully embedded ex-post enforcement mechanisms, responding to norm violations in ways to prevent repeated violation in the future and/or to demand compensation by executing actions prescribed in the system or in the norms (which may themselves by compliant or not)
* Loosely embedded ex-post enforcement mechanisms, responding to violations by communicating violations to components outside of the system as part of a request for "advice" on the action to be taken in response to the violation 
* Ex-post reflection mechanisms that, based on diagnostic reports and/or audit trails, propose changes to the current system and/or the norms that govern the system.

The example is centered around teachers -- running classes --, learners -- participating in classes -- and the caretakers of these learners. School regulations set norms around the setting and completing of assignments. Contracts between children and caretakers determine the conditions and consequences under which children can ask their caretakers for help with homework.
The example is an extension of the 'help with homework' example of the [paper on eFLINT](https://conf.researchr.org/details/gpce-2020/gpce2020/7/eFLINT-A-Domain-Specific-Language-for-Executable-Norm-Specifications) intended to, among other things, demonstrate the usage of eFLINT.

The folder `/doc` contains the description of the example as a benchmark, consisting of the norms that apply, a description of the software system, an informal explanation of related challenges and a collection of interesting scenarios that can be used as tests for proposed solutions.

The folder `/src` contains an example implementation of the system and scenarios, as described in `/doc`, without any consideration for the norms. The goal of a proposed solution is to produce an alternative system implementation, based on formal representation of the norms, in which the "positive" scenarios can occur and the "negative" scenarios are diagnosed as such without interrupting further execution of the system.

# eFLINT-based solution 

eFLINT is a domain-specific language for formalizing concepts, relations between concepts, powers and duties as found in sources of norms, as well as concrete scenarios that can be automatically checked for compliance.
The reactive component of the language admits runtime control and enforcement.
The contents of this folder serve to demonstrate the usage of eFLINT, and its integration as so-called _normative actors_ within [Scala Akka](https://doc.akka.io/docs/akka/current/typed/index.html) projects, with respect to the benchmark example provided by this repository.

Go [here](https://conf.researchr.org/details/gpce-2020/gpce2020/7/eFLINT-A-Domain-Specific-Language-for-Executable-Norm-Specifications) for a description of eFLINT and its usage within running systems.
