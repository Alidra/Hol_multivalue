require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3794808 [_98584 _98585] : Prf (∀ (λ f : El (fun _98585 (fun _98584 _98584)), (∀ (λ b : El _98584, (∀ (λ s : El (fun _98585 bool), (∀ (λ a : El _98584, (= ((@FINREC _98585 _98584) f b s a (SUC (NUMERAL _0))) (∃ (λ x : El _98585, (∧ (= s ((@INSERT _98585) x (@EMPTY _98585))) (= a (f x b))))))))))))));
