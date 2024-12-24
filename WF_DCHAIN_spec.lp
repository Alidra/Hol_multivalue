require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem316637 [A] (<< : El (fun A (fun A bool))) : Prf (= ((@WF A) <<) (¬ (∃ (λ s : El (fun num A), (∀ (λ n : El num, (<< (s (SUC n)) (s n))))))));
