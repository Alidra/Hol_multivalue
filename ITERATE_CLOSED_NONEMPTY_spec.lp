require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5809499 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ P : El (fun B bool), (⇒ (∀ (λ x : El B, (∀ (λ y : El B, (⇒ (∧ (P x) (P y)) (P (op x y))))))) (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∧ (¬ (= s (@EMPTY A))) (∀ (λ x : El A, (⇒ ((@IN A) x s) (P (f x))))))) (P ((@iterate B A) op s f)))))))))))));
