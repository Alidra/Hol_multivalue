require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3884187 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A (fun B bool)), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ ((@HAS_SIZE A) s m) (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@HAS_SIZE B) (t x) n)))) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (¬ (= x y)))) ((@DISJOINT B) (t x) (t y))))))))) ((@HAS_SIZE B) ((@UNIONS B) ((@GSPEC (fun B bool)) (λ GEN_PVAR_107 : El (fun B bool), (∃ (λ x : El A, ((@SETSPEC (fun B bool)) GEN_PVAR_107 ((@IN A) x s) (t x))))))) (* m n)))))))))));
