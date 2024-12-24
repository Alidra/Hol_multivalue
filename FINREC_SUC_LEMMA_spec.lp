require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3797397 [A B] : Prf (∀ (λ f : El (fun A (fun B B)), (∀ (λ b : El B, (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ s : El B, (⇒ (¬ (= x y)) (= (f x (f y s)) (f y (f x s)))))))))) (∀ (λ n : El num, (∀ (λ s : El (fun A bool), (∀ (λ z : El B, (⇒ ((@FINREC A B) f b s z (SUC n)) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∃ (λ w : El B, (∧ ((@FINREC A B) f b ((@DELETE A) s x) w n) (= z (f x w))))))))))))))))))));
