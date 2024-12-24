require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7036602 [A] : Prf (∀ (λ P : El (fun num bool), (∀ (λ f : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∧ (∀ (λ x : El num, (∀ (λ y : El num, (⇒ (∧ (P x) (P y)) (P (+ x y))))))) (∀ (λ a : El A, (⇒ ((@IN A) a s) (P (f a)))))))) (P ((@nsum A) s f)))))))));
