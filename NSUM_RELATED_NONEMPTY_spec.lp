require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7040763 [A] : Prf (∀ (λ R : El (fun num (fun num bool)), (∀ (λ f : El (fun A num), (∀ (λ g : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ (∧ (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ m' : El num, (∀ (λ n' : El num, (⇒ (∧ (R m n) (R m' n')) (R (+ m m') (+ n n'))))))))))) (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (R (f x) (g x)))))))) (R ((@nsum A) s f) ((@nsum A) s g)))))))))));
