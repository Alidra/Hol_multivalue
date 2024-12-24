require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7209759 [A] : Prf (∀ (λ R : El (fun real (fun real bool)), (∀ (λ f : El (fun A real), (∀ (λ g : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∧ (∀ (λ m : El real, (∀ (λ n : El real, (∀ (λ m' : El real, (∀ (λ n' : El real, (⇒ (∧ (R m n) (R m' n')) (R (real_add m m') (real_add n n'))))))))))) (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (R (f x) (g x)))))))) (R ((@sum A) s f) ((@sum A) s g)))))))))));
