require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4784136 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@INFINITE A) s) (∃ (λ f : El (fun num A), (∧ (∀ (λ x : El num, ((@IN A) (f x) s))) (∀ (λ x : El num, (∀ (λ y : El num, (⇒ (= (f x) (f y)) (= x y))))))))))));
