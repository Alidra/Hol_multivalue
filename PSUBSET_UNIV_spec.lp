require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3229314 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@PSUBSET A) s (@UNIV A)) (∃ (λ x : El A, (¬ ((@IN A) x s)))))));
