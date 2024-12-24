require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5737644 [_120271 _120280] (s : El (fun _120280 bool)) : Prf (∀ (λ op : El (fun _120271 (fun _120271 _120271)), (∀ (λ f : El (fun _120280 _120271), (∀ (λ a : El _120280, ((@FINITE _120280) ((@support _120280 _120271) op (λ x : El _120280, ((@COND _120271) (= x a) (f x) ((@neutral _120271) op))) s))))))));
