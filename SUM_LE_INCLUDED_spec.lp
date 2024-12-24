require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7196249 [A B] : Prf (∀ (λ f : El (fun A real), (∀ (λ g : El (fun B real), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ i : El (fun B A), (⇒ (∧ ((@FINITE A) s) (∧ ((@FINITE B) t) (∧ (∀ (λ y : El B, (⇒ ((@IN B) y t) (real_le (real_of_num (NUMERAL _0)) (g y))))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∃ (λ y : El B, (∧ ((@IN B) y t) (∧ (= (i y) x) (real_le (f x) (g y)))))))))))) (real_le ((@sum A) s f) ((@sum B) t g)))))))))))));
