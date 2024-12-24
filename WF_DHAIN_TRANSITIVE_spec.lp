require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem318095 [A] : Prf (∀ (λ << : El (fun A (fun A bool)), (⇒ (∀ (λ x : El A, (∀ (λ y : El A, (∀ (λ z : El A, (⇒ (∧ (<< x y) (<< y z)) (<< x z)))))))) (= ((@WF A) <<) (¬ (∃ (λ s : El (fun num A), (∀ (λ i : El num, (∀ (λ j : El num, (⇒ (< i j) (<< (s j) (s i))))))))))))));
