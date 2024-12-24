require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem13472 [A] (x : El A) (c : El bool) (P : El (fun A bool)) (y : El A) : Prf (= (P ((@COND A) c x y)) (∧ (⇒ c (P x)) (⇒ (¬ c) (P y))));
