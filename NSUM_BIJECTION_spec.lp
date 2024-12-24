require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7017950 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ p : El (fun A A), (∀ (λ s : El (fun A bool), (⇒ (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN A) (p x) s)))) (∀ (λ y : El A, (⇒ ((@IN A) y s) ((@∃! A) (λ x : El A, (∧ ((@IN A) x s) (= (p x) y)))))))) (= ((@nsum A) s f) ((@nsum A) s ((@o A A num) f p))))))))));
