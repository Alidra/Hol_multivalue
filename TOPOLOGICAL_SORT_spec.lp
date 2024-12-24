require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5700874 [A] : Prf (∀ (λ << : El (fun A (fun A bool)), (⇒ (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ (<< x y) (<< y x)) (= x y)))))) (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ z : El A, (⇒ (∧ (<< x y) (<< y z)) (<< x z))))))))) (∀ (λ n : El num, (∀ (λ s : El (fun A bool), (⇒ ((@HAS_SIZE A) s n) (∃ (λ f : El (fun num A), (∧ (= s ((@IMAGE num A) f (… (NUMERAL (BIT1 _0)) n))) (∀ (λ j : El num, (∀ (λ k : El num, (⇒ (∧ ((@IN num) j (… (NUMERAL (BIT1 _0)) n)) (∧ ((@IN num) k (… (NUMERAL (BIT1 _0)) n)) (< j k))) (¬ (<< (f k) (f j)))))))))))))))))));
