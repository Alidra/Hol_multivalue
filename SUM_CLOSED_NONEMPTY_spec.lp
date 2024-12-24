require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7205598 [A] : Prf (∀ (λ P : El (fun real bool), (∀ (λ f : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∧ (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (P x) (P y)) (P (real_add x y))))))) (∀ (λ a : El A, (⇒ ((@IN A) a s) (P (f a)))))))) (P ((@sum A) s f)))))))));
