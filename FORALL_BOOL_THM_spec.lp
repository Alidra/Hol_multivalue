require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem11006 (P : El (fun bool bool)) : Prf (= (∀ (λ b : El bool, (P b))) (∧ (P T) (P F)));
