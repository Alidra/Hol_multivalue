require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5782566 [A B] : Prf (∀ (λ op : El (fun B (fun B B)), (⇒ ((@monoidal B) op) (∀ (λ P : El (fun B bool), (⇒ (∧ (P ((@neutral B) op)) (∀ (λ x : El B, (∀ (λ y : El B, (⇒ (∧ (P x) (P y)) (P (op x y)))))))) (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∀ (λ x : El A, (⇒ (∧ ((@IN A) x s) (¬ (= (f x) ((@neutral B) op)))) (P (f x))))) (P ((@iterate B A) op s f)))))))))))));
