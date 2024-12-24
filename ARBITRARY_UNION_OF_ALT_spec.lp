require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4858243 [A] : Prf (∀ (λ B : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (= ((@UNION_OF A) (@ARBITRARY A) B s) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∃ (λ u : El (fun A bool), (∧ ((@IN (fun A bool)) u B) (∧ ((@IN A) x u) ((@SUBSET A) u s)))))))))))));
