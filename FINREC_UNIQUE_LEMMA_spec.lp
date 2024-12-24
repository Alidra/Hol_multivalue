require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3807377 [A B] : Prf (∀ (λ f : El (fun A (fun B B)), (∀ (λ b : El B, (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El B, (⇒ (¬ (= x y)) (= (f x (f y s)) (f y (f x s)))))))))) (∀ (λ n1 : El num, (∀ (λ n2 : El num, (∀ (λ s : El (fun A bool), (∀ (λ a1 : El B, (∀ (λ a2 : El B, (⇒ (∧ ((@FINREC A B) f b s a1 n1) ((@FINREC A B) f b s a2 n2)) (∧ (= a1 a2) (= n1 n2))))))))))))))))));
