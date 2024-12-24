require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1246844 (_22840 : El num) (_22841 : El num) (_22842 : El (fun num bool)) : Prf (= (_22842 (dist ((@̦‚ num num) _22841 _22840))) (∀ (λ d : El num, (∧ (⇒ (= _22841 (+ _22840 d)) (_22842 d)) (⇒ (= _22840 (+ _22841 d)) (_22842 d))))));
