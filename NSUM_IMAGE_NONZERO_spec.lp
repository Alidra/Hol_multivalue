require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7017843 [A B] : Prf (∀ (λ d : El (fun B num), (∀ (λ i : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (∧ (¬ (= x y)) (= (i x) (i y))))) (= (d (i x)) (NUMERAL _0)))))))) (= ((@nsum B) ((@IMAGE A B) i s) d) ((@nsum A) s ((@o A B num) d i))))))))));
