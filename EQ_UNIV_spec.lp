require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3216589 [A] (s : El (fun A bool)) : Prf (= (∀ (λ x : El A, ((@IN A) x s))) (= s (@UNIV A)));
