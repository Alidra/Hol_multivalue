require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1060000 [A] : Prf (∀ (λ c : El num, (∀ (λ i : El A, (∀ (λ r : El (fun num (recspace A)), (¬ (= ((@CONSTR A) c i r) (@BOTTOM A)))))))));
