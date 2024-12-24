require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7178038 [A B] : Prf (∀ (λ d : El (fun B real), (∀ (λ i : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (∧ (¬ (= x y)) (= (i x) (i y))))) (= (d (i x)) (real_of_num (NUMERAL _0))))))))) (= ((@sum B) ((@IMAGE A B) i s) d) ((@sum A) s ((@o A B real) d i))))))))));
