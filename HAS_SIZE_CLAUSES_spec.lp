require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3887954 [_100499] (n : El num) (s : El (fun _100499 bool)) : Prf (∧ (= ((@HAS_SIZE _100499) s (NUMERAL _0)) (= s (@EMPTY _100499))) (= ((@HAS_SIZE _100499) s (SUC n)) (∃ (λ a : El _100499, (∃ (λ t : El (fun _100499 bool), (∧ ((@HAS_SIZE _100499) t n) (∧ (¬ ((@IN _100499) a t)) (= s ((@INSERT _100499) a t))))))))));
