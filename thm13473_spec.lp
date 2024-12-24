require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem13473 [A] (_474 : El A) (_475 : El bool) (_476 : El (fun A bool)) (_477 : El A) : Prf (= (_476 ((@COND A) _475 _474 _477)) (∧ (⇒ _475 (_476 _474)) (⇒ (¬ _475) (_476 _477))));
