require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3867912 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ n : El num, (= ((@HAS_SIZE A) s (SUC n)) (∧ (¬ (= s (@EMPTY A))) (∀ (λ a : El A, (⇒ ((@IN A) a s) ((@HAS_SIZE A) ((@DELETE A) s a) n))))))))));
