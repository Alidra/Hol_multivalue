require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6920403 [A] (P : El (fun A bool)) (x : El A) : Prf ((λ x' : El A, (⇒ (∀ (λ y : El A, (= (P y) (= y x')))) (= ((@ε A) P) x'))) x);
