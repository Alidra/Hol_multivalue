require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4748800 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ n : El num, (⇒ ((@HAS_SIZE A) s n) (∃ (λ f : El (fun num A), (∧ (∀ (λ m : El num, (⇒ (< m n) ((@IN A) (f m) s)))) (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@∃! num) (λ m : El num, (∧ (< m n) (= (f m) x)))))))))))))));
