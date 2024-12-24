require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem13690 [_2843 _2845] : Prf (∀ (λ P : El (fun _2845 bool), (∀ (λ R : El (fun _2845 (fun _2843 bool)), (= (∀ (λ x : El _2845, (⇒ (P x) (∃ (λ y : El _2843, (R x y)))))) (∃ (λ f : El (fun _2845 _2843), (∀ (λ x : El _2845, (⇒ (P x) (R x (f x))))))))))));
