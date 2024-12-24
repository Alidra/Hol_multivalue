Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_RIGHT_INVERSE_term_abbrevs.
Require Import IN_UNIV_spec.
Require Import SURJECTIVE_ON_RIGHT_INVERSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem3570876 {_91307 _91308 : Type'} : term0 _91307 _91308.
Proof. exact (fun s : _91307 -> Prop => @lem3562737 _91307 _91308 s). Qed.
Lemma lem3570878 (p : Prop) : p = (term1 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3570879 {_91560 _91563 : Type'} (f : _91563 -> _91560) : ((term2 _91560 _91563 f) = (term3 _91560 _91563 f)) = (term4 _91560 _91563 f).
Proof. exact (@lem3570878 ((term2 _91560 _91563 f) = (term3 _91560 _91563 f))). Qed.
Lemma lem3570880 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term4 _91560 _91563 f) = ((term2 _91560 _91563 f) = (term3 _91560 _91563 f)).
Proof. exact (SYM (@lem3570879 _91560 _91563 f)). Qed.
Lemma lem3570881 {_91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term5 _91560 _91563 f.
Proof. exact (h1). Qed.
Lemma lem3570882 {_91307 _91560 : Type'} : term0 _91307 _91560.
Proof. exact (@lem3570876 _91307 _91560). Qed.
Lemma lem3570883 {_91560 : Type'} : term6 _91560.
Proof. exact (@lem3204818 _91560). Qed.
Lemma lem3570884 {_91307 : Type'} : term6 _91307.
Proof. exact (@lem3204818 _91307). Qed.
Lemma lem3570887 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term7 _91307 _91560 _91563 f) : term7 _91307 _91560 _91563 f.
Proof. exact (h1). Qed.
Lemma lem3570888 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : term8 _91307 _91560 _91563 f.
Proof. exact (fun h0 : term7 _91307 _91560 _91563 f => @lem3570887 _91307 _91560 _91563 f h0). Qed.
Lemma lem3570889 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term8 _91307 _91560 _91563 f) : term8 _91307 _91560 _91563 f.
Proof. exact (h1). Qed.
Lemma lem3570890 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term7 _91307 _91560 _91563 f) : term7 _91307 _91560 _91563 f.
Proof. exact (h1). Qed.
Lemma lem3570891 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term7 _91307 _91560 _91563 f) (h2 : term8 _91307 _91560 _91563 f) : term7 _91307 _91560 _91563 f.
Proof. exact (@lem3570889 _91307 _91560 _91563 f h2 (@lem3570890 _91307 _91560 _91563 f h1)). Qed.
Lemma lem3570892 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term7 _91307 _91560 _91563 f) : term9 _91307 _91560 _91563 f.
Proof. exact (fun h0 : term8 _91307 _91560 _91563 f => @lem3570891 _91307 _91560 _91563 f h1 h0). Qed.
Lemma lem3570893 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term8 _91307 _91560 _91563 f) : term8 _91307 _91560 _91563 f.
Proof. exact (h1). Qed.
Lemma lem3570894 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term7 _91307 _91560 _91563 f) (h2 : term8 _91307 _91560 _91563 f) : term7 _91307 _91560 _91563 f.
Proof. exact (@lem3570892 _91307 _91560 _91563 f h1 (@lem3570893 _91307 _91560 _91563 f h2)). Qed.
Lemma lem3570895 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term8 _91307 _91560 _91563 f) : term8 _91307 _91560 _91563 f.
Proof. exact (fun h0 : term7 _91307 _91560 _91563 f => @lem3570894 _91307 _91560 _91563 f h0 h1). Qed.
Lemma lem3570896 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : term10 _91307 _91560 _91563 f.
Proof. exact (fun h0 : term8 _91307 _91560 _91563 f => @lem3570895 _91307 _91560 _91563 f h0). Qed.
Lemma lem3570899 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : term8 _91307 _91560 _91563 f.
Proof. exact (@lem3570896 _91307 _91560 _91563 f (@lem3570888 _91307 _91560 _91563 f)). Qed.
Lemma lem3570900 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : term8 _91307 _91560 _91563 f.
Proof. exact (@lem3570899 _91307 _91560 _91563 f). Qed.
Lemma lem3570936 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3570937 {_91307 _91560 : Type'} : (term11 _91307 _91560) = (term12 _91307 _91560).
Proof. exact (@lem3570936 (term0 _91307 _91560)). Qed.
Lemma lem3571018 {_91560 : Type'} : (term13 _91560) = (term13 _91560).
Proof. exact (eq_refl (term13 _91560)). Qed.
Lemma lem3571019 {_91307 _91560 : Type'} : (term14 _91307 _91560) = (term15 _91307 _91560).
Proof. exact (MK_COMB (@lem3571018 _91560) (@lem3570937 _91307 _91560)). Qed.
Lemma lem3571022 {_91307 : Type'} : (term13 _91307) = (term13 _91307).
Proof. exact (eq_refl (term13 _91307)). Qed.
Lemma lem3571023 {_91307 _91560 : Type'} : (term16 _91307 _91560) = (term17 _91307 _91560).
Proof. exact (MK_COMB (@lem3571022 _91307) (@lem3571019 _91307 _91560)). Qed.
Lemma lem3571026 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term18 _91560 _91563 f) = (term18 _91560 _91563 f).
Proof. exact (eq_refl (term18 _91560 _91563 f)). Qed.
Lemma lem3571027 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : (term7 _91307 _91560 _91563 f) = (term19 _91307 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571026 _91560 _91563 f) (@lem3571023 _91307 _91560)). Qed.
Lemma lem3571030 {_91307 _91560 _91563 : Type'} : (term20 _91307 _91560 _91563) = (term21 _91307 _91560 _91563).
Proof. exact (fun_ext (fun f : _91563 -> _91560 => @lem3571027 _91307 _91560 _91563 f)). Qed.
Lemma lem3571031 {_91560 _91563 : Type'} : (@all (_91563 -> _91560)) = (@all (_91563 -> _91560)).
Proof. exact (eq_refl (@all (_91563 -> _91560))). Qed.
Lemma lem3571040 {_91307 _91560 _91563 : Type'} : (term22 _91307 _91560 _91563) = (term23 _91307 _91560 _91563).
Proof. exact (MK_COMB (@lem3571031 _91560 _91563) (@lem3571030 _91307 _91560 _91563)). Qed.
Lemma lem3571049 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term24 _91307 _91560 t s f g y) = (term24 _91307 _91560 t s f g y).
Proof. exact (eq_refl (term24 _91307 _91560 t s f g y)). Qed.
Lemma lem3571050 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term25 _91307 _91560 t s f g) = (term25 _91307 _91560 t s f g).
Proof. exact (fun_ext (fun y : _91560 => @lem3571049 _91307 _91560 t s f g y)). Qed.
Lemma lem3571051 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571052 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term26 _91307 _91560 t s f g) = (term26 _91307 _91560 t s f g).
Proof. exact (MK_COMB (@lem3571051 _91560) (@lem3571050 _91307 _91560 t s f g)). Qed.
Lemma lem3571053 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term27 _91307 _91560 t s f) = (term27 _91307 _91560 t s f).
Proof. exact (fun_ext (fun g : _91560 -> _91307 => @lem3571052 _91307 _91560 t s f g)). Qed.
Lemma lem3571054 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3571055 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term28 _91307 _91560 t s f) = (term28 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571054 _91307 _91560) (@lem3571053 _91307 _91560 t s f)). Qed.
Lemma lem3571060 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term29 _91307 _91560 s f x y) = (term29 _91307 _91560 s f x y).
Proof. exact (eq_refl (term29 _91307 _91560 s f x y)). Qed.
Lemma lem3571061 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term30 _91307 _91560 s f y) = (term30 _91307 _91560 s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3571060 _91307 _91560 s f x y)). Qed.
Lemma lem3571062 {_91307 : Type'} : (@ex _91307) = (@ex _91307).
Proof. exact (eq_refl (@ex _91307)). Qed.
Lemma lem3571063 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term31 _91307 _91560 s f y) = (term31 _91307 _91560 s f y).
Proof. exact (MK_COMB (@lem3571062 _91307) (@lem3571061 _91307 _91560 s f y)). Qed.
Lemma lem3571066 {_91560 : Type'} (y : _91560) (t : _91560 -> Prop) : (term32 _91560 y t) = (term32 _91560 y t).
Proof. exact (eq_refl (term32 _91560 y t)). Qed.
Lemma lem3571067 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term33 _91307 _91560 t s f y) = (term33 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3571066 _91560 y t) (@lem3571063 _91307 _91560 s f y)). Qed.
Lemma lem3571068 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term34 _91307 _91560 t s f) = (term34 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571067 _91307 _91560 t s f y)). Qed.
Lemma lem3571069 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571070 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term35 _91307 _91560 t s f) = (term35 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571069 _91560) (@lem3571068 _91307 _91560 t s f)). Qed.
Lemma lem3571071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571072 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term36 _91307 _91560 t s f) = (term36 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571071) (@lem3571070 _91307 _91560 t s f)). Qed.
Lemma lem3571073 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term35 _91307 _91560 t s f) = (term28 _91307 _91560 t s f)) = ((term35 _91307 _91560 t s f) = (term28 _91307 _91560 t s f)).
Proof. exact (MK_COMB (@lem3571072 _91307 _91560 t s f) (@lem3571055 _91307 _91560 t s f)). Qed.
Lemma lem3571074 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term37 _91307 _91560 s f) = (term37 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3571073 _91307 _91560 t s f)). Qed.
Lemma lem3571075 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3571076 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term38 _91307 _91560 s f) = (term38 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3571075 _91560) (@lem3571074 _91307 _91560 s f)). Qed.
Lemma lem3571077 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term39 _91307 _91560 s) = (term39 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3571076 _91307 _91560 s f)). Qed.
Lemma lem3571078 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3571079 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term40 _91307 _91560 s) = (term40 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3571078 _91307 _91560) (@lem3571077 _91307 _91560 s)). Qed.
Lemma lem3571080 {_91307 _91560 : Type'} : (term41 _91307 _91560) = (term41 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3571079 _91307 _91560 s)). Qed.
Lemma lem3571081 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3571082 {_91307 _91560 : Type'} : (term0 _91307 _91560) = (term0 _91307 _91560).
Proof. exact (MK_COMB (@lem3571081 _91307) (@lem3571080 _91307 _91560)). Qed.
Lemma lem3571083 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571084 {_91307 _91560 : Type'} : (term12 _91307 _91560) = (term12 _91307 _91560).
Proof. exact (MK_COMB (@lem3571083) (@lem3571082 _91307 _91560)). Qed.
Lemma lem3571085 {_91560 : Type'} (x : _91560) : (@IN _91560 x (@UNIV _91560)) = (@IN _91560 x (@UNIV _91560)).
Proof. exact (eq_refl (@IN _91560 x (@UNIV _91560))). Qed.
Lemma lem3571086 {_91560 : Type'} : (term42 _91560) = (term42 _91560).
Proof. exact (fun_ext (fun x : _91560 => @lem3571085 _91560 x)). Qed.
Lemma lem3571087 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571088 {_91560 : Type'} : (term6 _91560) = (term6 _91560).
Proof. exact (MK_COMB (@lem3571087 _91560) (@lem3571086 _91560)). Qed.
Lemma lem3571089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3571090 {_91560 : Type'} : (term13 _91560) = (term13 _91560).
Proof. exact (MK_COMB (@lem3571089) (@lem3571088 _91560)). Qed.
Lemma lem3571091 {_91307 _91560 : Type'} : (term15 _91307 _91560) = (term15 _91307 _91560).
Proof. exact (MK_COMB (@lem3571090 _91560) (@lem3571084 _91307 _91560)). Qed.
Lemma lem3571092 {_91307 : Type'} (x : _91307) : (@IN _91307 x (@UNIV _91307)) = (@IN _91307 x (@UNIV _91307)).
Proof. exact (eq_refl (@IN _91307 x (@UNIV _91307))). Qed.
Lemma lem3571093 {_91307 : Type'} : (term42 _91307) = (term42 _91307).
Proof. exact (fun_ext (fun x : _91307 => @lem3571092 _91307 x)). Qed.
Lemma lem3571094 {_91307 : Type'} : (@all _91307) = (@all _91307).
Proof. exact (eq_refl (@all _91307)). Qed.
Lemma lem3571095 {_91307 : Type'} : (term6 _91307) = (term6 _91307).
Proof. exact (MK_COMB (@lem3571094 _91307) (@lem3571093 _91307)). Qed.
Lemma lem3571096 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3571097 {_91307 : Type'} : (term13 _91307) = (term13 _91307).
Proof. exact (MK_COMB (@lem3571096) (@lem3571095 _91307)). Qed.
Lemma lem3571098 {_91307 _91560 : Type'} : (term17 _91307 _91560) = (term17 _91307 _91560).
Proof. exact (MK_COMB (@lem3571097 _91307) (@lem3571091 _91307 _91560)). Qed.
Lemma lem3571099 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) (y : _91560) : ((term43 _91560 _91563 f g y) = y) = ((term43 _91560 _91563 f g y) = y).
Proof. exact (eq_refl ((term43 _91560 _91563 f g y) = y)). Qed.
Lemma lem3571100 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term44 _91560 _91563 f g) = (term44 _91560 _91563 f g).
Proof. exact (fun_ext (fun y : _91560 => @lem3571099 _91560 _91563 f g y)). Qed.
Lemma lem3571101 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571102 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term45 _91560 _91563 f g) = (term45 _91560 _91563 f g).
Proof. exact (MK_COMB (@lem3571101 _91560) (@lem3571100 _91560 _91563 f g)). Qed.
Lemma lem3571103 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term46 _91560 _91563 f) = (term46 _91560 _91563 f).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571102 _91560 _91563 f g)). Qed.
Lemma lem3571104 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571105 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term3 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571104 _91560 _91563) (@lem3571103 _91560 _91563 f)). Qed.
Lemma lem3571106 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y : _91560) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3571107 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term47 _91560 _91563 f y) = (term47 _91560 _91563 f y).
Proof. exact (fun_ext (fun x : _91563 => @lem3571106 _91560 _91563 f x y)). Qed.
Lemma lem3571108 {_91563 : Type'} : (@ex _91563) = (@ex _91563).
Proof. exact (eq_refl (@ex _91563)). Qed.
Lemma lem3571109 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term48 _91560 _91563 f y) = (term48 _91560 _91563 f y).
Proof. exact (MK_COMB (@lem3571108 _91563) (@lem3571107 _91560 _91563 f y)). Qed.
Lemma lem3571110 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term49 _91560 _91563 f) = (term49 _91560 _91563 f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571109 _91560 _91563 f y)). Qed.
Lemma lem3571111 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571112 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term2 _91560 _91563 f) = (term2 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571111 _91560) (@lem3571110 _91560 _91563 f)). Qed.
Lemma lem3571113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571114 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term50 _91560 _91563 f) = (term50 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571113) (@lem3571112 _91560 _91563 f)). Qed.
Lemma lem3571115 {_91560 _91563 : Type'} (f : _91563 -> _91560) : ((term2 _91560 _91563 f) = (term3 _91560 _91563 f)) = ((term2 _91560 _91563 f) = (term3 _91560 _91563 f)).
Proof. exact (MK_COMB (@lem3571114 _91560 _91563 f) (@lem3571105 _91560 _91563 f)). Qed.
Lemma lem3571116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571117 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term5 _91560 _91563 f) = (term5 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571116) (@lem3571115 _91560 _91563 f)). Qed.
Lemma lem3571118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3571119 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term18 _91560 _91563 f) = (term18 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571118) (@lem3571117 _91560 _91563 f)). Qed.
Lemma lem3571120 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : (term19 _91307 _91560 _91563 f) = (term19 _91307 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571119 _91560 _91563 f) (@lem3571098 _91307 _91560)). Qed.
Lemma lem3571121 {_91307 _91560 _91563 : Type'} : (term21 _91307 _91560 _91563) = (term21 _91307 _91560 _91563).
Proof. exact (fun_ext (fun f : _91563 -> _91560 => @lem3571120 _91307 _91560 _91563 f)). Qed.
Lemma lem3571122 {_91560 _91563 : Type'} : (@all (_91563 -> _91560)) = (@all (_91563 -> _91560)).
Proof. exact (eq_refl (@all (_91563 -> _91560))). Qed.
Lemma lem3571123 {_91307 _91560 _91563 : Type'} : (term23 _91307 _91560 _91563) = (term23 _91307 _91560 _91563).
Proof. exact (MK_COMB (@lem3571122 _91560 _91563) (@lem3571121 _91307 _91560 _91563)). Qed.
Lemma lem3571224 {_91307 _91560 _91563 : Type'} : (term22 _91307 _91560 _91563) = (term23 _91307 _91560 _91563).
Proof. exact (TRANS (@lem3571040 _91307 _91560 _91563) (@lem3571123 _91307 _91560 _91563)). Qed.
Lemma lem3571225 {_91307 _91560 _91563 : Type'} : (term23 _91307 _91560 _91563) = (term22 _91307 _91560 _91563).
Proof. exact (SYM (@lem3571224 _91307 _91560 _91563)). Qed.
Lemma lem3571226 {_91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term5 _91560 _91563 f.
Proof. exact (h1). Qed.
Lemma lem3571229 {_91307 _91560 : Type'} (h1 : term0 _91307 _91560) : term0 _91307 _91560.
Proof. exact (h1). Qed.
Lemma lem3571231 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y : _91560) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3571232 {_91563 : Type'} (P : _91563 -> Prop) : (term51 _91563 P) = (term52 _91563 P).
Proof. exact (@lem18394 _91563 P). Qed.
Lemma lem3571233 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term53 _91560 _91563 f y) = (term54 _91560 _91563 f y).
Proof. exact (@lem3571232 _91563 (term47 _91560 _91563 f y)). Qed.
Lemma lem3571234 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y : _91560) : (term55 _91560 _91563 f y x) = ((f x) = y).
Proof. exact (eq_refl (term55 _91560 _91563 f y x)). Qed.
Lemma lem3571235 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571237 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y : _91560) : (term56 _91560 _91563 f y x) = (term57 _91560 _91563 f x y).
Proof. exact (MK_COMB (@lem3571235) (@lem3571234 _91560 _91563 f x y)). Qed.
Lemma lem3571238 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term58 _91560 _91563 f y) = (term59 _91560 _91563 f y).
Proof. exact (fun_ext (fun x : _91563 => @lem3571237 _91560 _91563 f x y)). Qed.
Lemma lem3571239 {_91563 : Type'} : (@all _91563) = (@all _91563).
Proof. exact (eq_refl (@all _91563)). Qed.
Lemma lem3571240 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term54 _91560 _91563 f y) = (term60 _91560 _91563 f y).
Proof. exact (MK_COMB (@lem3571239 _91563) (@lem3571238 _91560 _91563 f y)). Qed.
Lemma lem3571241 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term53 _91560 _91563 f y) = (term60 _91560 _91563 f y).
Proof. exact (TRANS (@lem3571233 _91560 _91563 f y) (@lem3571240 _91560 _91563 f y)). Qed.
Lemma lem3571242 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term47 _91560 _91563 f y) = (term47 _91560 _91563 f y).
Proof. exact (fun_ext (fun x : _91563 => @lem3571231 _91560 _91563 f x y)). Qed.
Lemma lem3571243 {_91563 : Type'} : (@ex _91563) = (@ex _91563).
Proof. exact (eq_refl (@ex _91563)). Qed.
Lemma lem3571244 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term48 _91560 _91563 f y) = (term48 _91560 _91563 f y).
Proof. exact (MK_COMB (@lem3571243 _91563) (@lem3571242 _91560 _91563 f y)). Qed.
Lemma lem3571245 {_91560 : Type'} (P : _91560 -> Prop) : (term61 _91560 P) = (term62 _91560 P).
Proof. exact (@lem18392 _91560 P). Qed.
Lemma lem3571246 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term63 _91560 _91563 f) = (term64 _91560 _91563 f).
Proof. exact (@lem3571245 _91560 (term49 _91560 _91563 f)). Qed.
Lemma lem3571247 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term65 _91560 _91563 f y) = (term48 _91560 _91563 f y).
Proof. exact (eq_refl (term65 _91560 _91563 f y)). Qed.
Lemma lem3571248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571249 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term66 _91560 _91563 f y) = (term53 _91560 _91563 f y).
Proof. exact (MK_COMB (@lem3571248) (@lem3571247 _91560 _91563 f y)). Qed.
Lemma lem3571250 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term66 _91560 _91563 f y) = (term60 _91560 _91563 f y).
Proof. exact (TRANS (@lem3571249 _91560 _91563 f y) (@lem3571241 _91560 _91563 f y)). Qed.
Lemma lem3571251 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term67 _91560 _91563 f) = (term68 _91560 _91563 f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571250 _91560 _91563 f y)). Qed.
Lemma lem3571252 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571253 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term64 _91560 _91563 f) = (term69 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571252 _91560) (@lem3571251 _91560 _91563 f)). Qed.
Lemma lem3571254 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term63 _91560 _91563 f) = (term69 _91560 _91563 f).
Proof. exact (TRANS (@lem3571246 _91560 _91563 f) (@lem3571253 _91560 _91563 f)). Qed.
Lemma lem3571255 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term49 _91560 _91563 f) = (term49 _91560 _91563 f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571244 _91560 _91563 f y)). Qed.
Lemma lem3571256 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571257 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term2 _91560 _91563 f) = (term2 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571256 _91560) (@lem3571255 _91560 _91563 f)). Qed.
Lemma lem3571259 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) (y : _91560) : ((term43 _91560 _91563 f g y) = y) = ((term43 _91560 _91563 f g y) = y).
Proof. exact (eq_refl ((term43 _91560 _91563 f g y) = y)). Qed.
Lemma lem3571260 {_91560 : Type'} (P : _91560 -> Prop) : (term61 _91560 P) = (term62 _91560 P).
Proof. exact (@lem18392 _91560 P). Qed.
Lemma lem3571261 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term70 _91560 _91563 f g) = (term71 _91560 _91563 f g).
Proof. exact (@lem3571260 _91560 (term44 _91560 _91563 f g)). Qed.
Lemma lem3571262 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) (y : _91560) : (term72 _91560 _91563 f g y) = ((term43 _91560 _91563 f g y) = y).
Proof. exact (eq_refl (term72 _91560 _91563 f g y)). Qed.
Lemma lem3571263 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571265 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) (y : _91560) : (term73 _91560 _91563 f g y) = (term74 _91560 _91563 f g y).
Proof. exact (MK_COMB (@lem3571263) (@lem3571262 _91560 _91563 f g y)). Qed.
Lemma lem3571266 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term75 _91560 _91563 f g) = (term76 _91560 _91563 f g).
Proof. exact (fun_ext (fun y : _91560 => @lem3571265 _91560 _91563 f g y)). Qed.
Lemma lem3571267 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571268 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term71 _91560 _91563 f g) = (term77 _91560 _91563 f g).
Proof. exact (MK_COMB (@lem3571267 _91560) (@lem3571266 _91560 _91563 f g)). Qed.
Lemma lem3571269 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term70 _91560 _91563 f g) = (term77 _91560 _91563 f g).
Proof. exact (TRANS (@lem3571261 _91560 _91563 f g) (@lem3571268 _91560 _91563 f g)). Qed.
Lemma lem3571270 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term44 _91560 _91563 f g) = (term44 _91560 _91563 f g).
Proof. exact (fun_ext (fun y : _91560 => @lem3571259 _91560 _91563 f g y)). Qed.
Lemma lem3571271 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571272 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term45 _91560 _91563 f g) = (term45 _91560 _91563 f g).
Proof. exact (MK_COMB (@lem3571271 _91560) (@lem3571270 _91560 _91563 f g)). Qed.
Lemma lem3571273 {_91560 _91563 : Type'} (P : type572 _91560 _91563) : (term78 _91560 _91563 P) = (term79 _91560 _91563 P).
Proof. exact (@lem18394 (_91560 -> _91563) P). Qed.
Lemma lem3571274 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term80 _91560 _91563 f) = (term81 _91560 _91563 f).
Proof. exact (@lem3571273 _91560 _91563 (term46 _91560 _91563 f)). Qed.
Lemma lem3571275 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term82 _91560 _91563 f g) = (term45 _91560 _91563 f g).
Proof. exact (eq_refl (term82 _91560 _91563 f g)). Qed.
Lemma lem3571276 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571277 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term83 _91560 _91563 f g) = (term70 _91560 _91563 f g).
Proof. exact (MK_COMB (@lem3571276) (@lem3571275 _91560 _91563 f g)). Qed.
Lemma lem3571278 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term83 _91560 _91563 f g) = (term77 _91560 _91563 f g).
Proof. exact (TRANS (@lem3571277 _91560 _91563 f g) (@lem3571269 _91560 _91563 f g)). Qed.
Lemma lem3571279 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term84 _91560 _91563 f) = (term85 _91560 _91563 f).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571278 _91560 _91563 f g)). Qed.
Lemma lem3571280 {_91560 _91563 : Type'} : (@all (_91560 -> _91563)) = (@all (_91560 -> _91563)).
Proof. exact (eq_refl (@all (_91560 -> _91563))). Qed.
Lemma lem3571281 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term81 _91560 _91563 f) = (term86 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571280 _91560 _91563) (@lem3571279 _91560 _91563 f)). Qed.
Lemma lem3571282 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term80 _91560 _91563 f) = (term86 _91560 _91563 f).
Proof. exact (TRANS (@lem3571274 _91560 _91563 f) (@lem3571281 _91560 _91563 f)). Qed.
Lemma lem3571283 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term46 _91560 _91563 f) = (term46 _91560 _91563 f).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571272 _91560 _91563 f g)). Qed.
Lemma lem3571284 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571285 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term3 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571284 _91560 _91563) (@lem3571283 _91560 _91563 f)). Qed.
Lemma lem3571286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571287 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term87 _91560 _91563 f) = (term88 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571286) (@lem3571254 _91560 _91563 f)). Qed.
Lemma lem3571288 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term89 _91560 _91563 f) = (term90 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571287 _91560 _91563 f) (@lem3571285 _91560 _91563 f)). Qed.
Lemma lem3571289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571290 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term91 _91560 _91563 f) = (term91 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571289) (@lem3571257 _91560 _91563 f)). Qed.
Lemma lem3571291 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term92 _91560 _91563 f) = (term93 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571290 _91560 _91563 f) (@lem3571282 _91560 _91563 f)). Qed.
Lemma lem3571292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3571293 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term94 _91560 _91563 f) = (term95 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571292) (@lem3571291 _91560 _91563 f)). Qed.
Lemma lem3571294 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term96 _91560 _91563 f) = (term97 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571293 _91560 _91563 f) (@lem3571288 _91560 _91563 f)). Qed.
Lemma lem3571295 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term5 _91560 _91563 f) = (term96 _91560 _91563 f).
Proof. exact (@lem17646 (term2 _91560 _91563 f) (term3 _91560 _91563 f)). Qed.
Lemma lem3571296 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term5 _91560 _91563 f) = (term97 _91560 _91563 f).
Proof. exact (TRANS (@lem3571295 _91560 _91563 f) (@lem3571294 _91560 _91563 f)). Qed.
Lemma lem3571331 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3571332 {_91560 _91563 : Type'} (P : type1413 _91560 _91563) : (term98 _91560 _91563 P) = (term99 _91560 _91563 P).
Proof. exact (@lem3571331 _91560 _91563 P). Qed.
Lemma lem3571333 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term100 _91560 _91563 f) = (term101 _91560 _91563 f).
Proof. exact (@lem3571332 _91560 _91563 (term102 _91560 _91563 f)). Qed.
Lemma lem3571334 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term103 _91560 _91563 f y) = (term47 _91560 _91563 f y).
Proof. exact (eq_refl (term103 _91560 _91563 f y)). Qed.
Lemma lem3571335 {_91563 : Type'} (x : _91563) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3571336 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) (x : _91563) : (term104 _91560 _91563 f y x) = (term55 _91560 _91563 f y x).
Proof. exact (MK_COMB (@lem3571334 _91560 _91563 f y) (@lem3571335 _91563 x)). Qed.
Lemma lem3571337 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y : _91560) : (term55 _91560 _91563 f y x) = ((f x) = y).
Proof. exact (eq_refl (term55 _91560 _91563 f y x)). Qed.
Lemma lem3571338 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y : _91560) : (term104 _91560 _91563 f y x) = ((f x) = y).
Proof. exact (TRANS (@lem3571336 _91560 _91563 f y x) (@lem3571337 _91560 _91563 f x y)). Qed.
Lemma lem3571339 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term105 _91560 _91563 f y) = (term47 _91560 _91563 f y).
Proof. exact (fun_ext (fun x : _91563 => @lem3571338 _91560 _91563 f x y)). Qed.
Lemma lem3571340 {_91563 : Type'} : (@ex _91563) = (@ex _91563).
Proof. exact (eq_refl (@ex _91563)). Qed.
Lemma lem3571341 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term106 _91560 _91563 f y) = (term48 _91560 _91563 f y).
Proof. exact (MK_COMB (@lem3571340 _91563) (@lem3571339 _91560 _91563 f y)). Qed.
Lemma lem3571342 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term107 _91560 _91563 f) = (term49 _91560 _91563 f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571341 _91560 _91563 f y)). Qed.
Lemma lem3571343 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571344 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term100 _91560 _91563 f) = (term2 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571343 _91560) (@lem3571342 _91560 _91563 f)). Qed.
Lemma lem3571345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571346 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term108 _91560 _91563 f) = (term50 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571345) (@lem3571344 _91560 _91563 f)). Qed.
Lemma lem3571347 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term103 _91560 _91563 f y) = (term47 _91560 _91563 f y).
Proof. exact (eq_refl (term103 _91560 _91563 f y)). Qed.
Lemma lem3571348 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : _91560) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3571349 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) (y : _91560) : (term109 _91560 _91563 f x y) = (term110 _91560 _91563 f x y).
Proof. exact (MK_COMB (@lem3571347 _91560 _91563 f y) (@lem3571348 _91560 _91563 x y)). Qed.
Lemma lem3571350 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) (y : _91560) : (term110 _91560 _91563 f x y) = ((term43 _91560 _91563 f x y) = y).
Proof. exact (eq_refl (term110 _91560 _91563 f x y)). Qed.
Lemma lem3571351 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) (y : _91560) : (term109 _91560 _91563 f x y) = ((term43 _91560 _91563 f x y) = y).
Proof. exact (TRANS (@lem3571349 _91560 _91563 f x y) (@lem3571350 _91560 _91563 f x y)). Qed.
Lemma lem3571352 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) : (term111 _91560 _91563 f x) = (term44 _91560 _91563 f x).
Proof. exact (fun_ext (fun y : _91560 => @lem3571351 _91560 _91563 f x y)). Qed.
Lemma lem3571353 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571354 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) : (term112 _91560 _91563 f x) = (term45 _91560 _91563 f x).
Proof. exact (MK_COMB (@lem3571353 _91560) (@lem3571352 _91560 _91563 f x)). Qed.
Lemma lem3571355 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term113 _91560 _91563 f) = (term46 _91560 _91563 f).
Proof. exact (fun_ext (fun x : _91560 -> _91563 => @lem3571354 _91560 _91563 f x)). Qed.
Lemma lem3571356 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571357 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term101 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571356 _91560 _91563) (@lem3571355 _91560 _91563 f)). Qed.
Lemma lem3571358 {_91560 _91563 : Type'} (f : _91563 -> _91560) : ((term100 _91560 _91563 f) = (term101 _91560 _91563 f)) = ((term2 _91560 _91563 f) = (term3 _91560 _91563 f)).
Proof. exact (MK_COMB (@lem3571346 _91560 _91563 f) (@lem3571357 _91560 _91563 f)). Qed.
Lemma lem3571359 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term2 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (EQ_MP (@lem3571358 _91560 _91563 f) (@lem3571333 _91560 _91563 f)). Qed.
Lemma lem3571360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571361 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term91 _91560 _91563 f) = (term114 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571360) (@lem3571359 _91560 _91563 f)). Qed.
Lemma lem3571363 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3571364 {_91560 _91563 : Type'} (P : type551 _91560 _91563) : (term115 _91560 _91563 P) = (term116 _91560 _91563 P).
Proof. exact (@lem3571363 (_91560 -> _91563) _91560 P). Qed.
Lemma lem3571365 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term117 _91560 _91563 f) = (term118 _91560 _91563 f).
Proof. exact (@lem3571364 _91560 _91563 (term119 _91560 _91563 f)). Qed.
Lemma lem3571366 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term120 _91560 _91563 f g) = (term76 _91560 _91563 f g).
Proof. exact (eq_refl (term120 _91560 _91563 f g)). Qed.
Lemma lem3571367 {_91560 : Type'} (y : _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3571368 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) (y : _91560) : (term121 _91560 _91563 f g y) = (term122 _91560 _91563 f g y).
Proof. exact (MK_COMB (@lem3571366 _91560 _91563 f g) (@lem3571367 _91560 y)). Qed.
Lemma lem3571369 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) (y : _91560) : (term122 _91560 _91563 f g y) = (term74 _91560 _91563 f g y).
Proof. exact (eq_refl (term122 _91560 _91563 f g y)). Qed.
Lemma lem3571370 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) (y : _91560) : (term121 _91560 _91563 f g y) = (term74 _91560 _91563 f g y).
Proof. exact (TRANS (@lem3571368 _91560 _91563 f g y) (@lem3571369 _91560 _91563 f g y)). Qed.
Lemma lem3571371 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term123 _91560 _91563 f g) = (term76 _91560 _91563 f g).
Proof. exact (fun_ext (fun y : _91560 => @lem3571370 _91560 _91563 f g y)). Qed.
Lemma lem3571372 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571373 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term124 _91560 _91563 f g) = (term77 _91560 _91563 f g).
Proof. exact (MK_COMB (@lem3571372 _91560) (@lem3571371 _91560 _91563 f g)). Qed.
Lemma lem3571374 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term125 _91560 _91563 f) = (term85 _91560 _91563 f).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571373 _91560 _91563 f g)). Qed.
Lemma lem3571375 {_91560 _91563 : Type'} : (@all (_91560 -> _91563)) = (@all (_91560 -> _91563)).
Proof. exact (eq_refl (@all (_91560 -> _91563))). Qed.
Lemma lem3571376 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term117 _91560 _91563 f) = (term86 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571375 _91560 _91563) (@lem3571374 _91560 _91563 f)). Qed.
Lemma lem3571377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571378 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term126 _91560 _91563 f) = (term127 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571377) (@lem3571376 _91560 _91563 f)). Qed.
Lemma lem3571379 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term120 _91560 _91563 f g) = (term76 _91560 _91563 f g).
Proof. exact (eq_refl (term120 _91560 _91563 f g)). Qed.
Lemma lem3571380 {_91560 _91563 : Type'} (y : type569 _91560 _91563) (g : _91560 -> _91563) : (y g) = (y g).
Proof. exact (eq_refl (y g)). Qed.
Lemma lem3571381 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : type569 _91560 _91563) (g : _91560 -> _91563) : (term128 _91560 _91563 f y g) = (term129 _91560 _91563 f y g).
Proof. exact (MK_COMB (@lem3571379 _91560 _91563 f g) (@lem3571380 _91560 _91563 y g)). Qed.
Lemma lem3571382 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : type569 _91560 _91563) (g : _91560 -> _91563) : (term129 _91560 _91563 f y g) = (term130 _91560 _91563 f y g).
Proof. exact (eq_refl (term129 _91560 _91563 f y g)). Qed.
Lemma lem3571383 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : type569 _91560 _91563) (g : _91560 -> _91563) : (term128 _91560 _91563 f y g) = (term130 _91560 _91563 f y g).
Proof. exact (TRANS (@lem3571381 _91560 _91563 f y g) (@lem3571382 _91560 _91563 f y g)). Qed.
Lemma lem3571384 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term131 _91560 _91563 f y) = (term132 _91560 _91563 f y).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571383 _91560 _91563 f y g)). Qed.
Lemma lem3571385 {_91560 _91563 : Type'} : (@all (_91560 -> _91563)) = (@all (_91560 -> _91563)).
Proof. exact (eq_refl (@all (_91560 -> _91563))). Qed.
Lemma lem3571386 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term133 _91560 _91563 f y) = (term134 _91560 _91563 f y).
Proof. exact (MK_COMB (@lem3571385 _91560 _91563) (@lem3571384 _91560 _91563 f y)). Qed.
Lemma lem3571387 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term135 _91560 _91563 f) = (term136 _91560 _91563 f).
Proof. exact (fun_ext (fun y : type569 _91560 _91563 => @lem3571386 _91560 _91563 f y)). Qed.
Lemma lem3571388 {_91560 _91563 : Type'} : (@ex ((_91560 -> _91563) -> _91560)) = (@ex ((_91560 -> _91563) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91563) -> _91560))). Qed.
Lemma lem3571389 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term118 _91560 _91563 f) = (term137 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571388 _91560 _91563) (@lem3571387 _91560 _91563 f)). Qed.
Lemma lem3571390 {_91560 _91563 : Type'} (f : _91563 -> _91560) : ((term117 _91560 _91563 f) = (term118 _91560 _91563 f)) = ((term86 _91560 _91563 f) = (term137 _91560 _91563 f)).
Proof. exact (MK_COMB (@lem3571378 _91560 _91563 f) (@lem3571389 _91560 _91563 f)). Qed.
Lemma lem3571391 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term86 _91560 _91563 f) = (term137 _91560 _91563 f).
Proof. exact (EQ_MP (@lem3571390 _91560 _91563 f) (@lem3571365 _91560 _91563 f)). Qed.
Lemma lem3571392 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term93 _91560 _91563 f) = (term138 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571361 _91560 _91563 f) (@lem3571391 _91560 _91563 f)). Qed.
Lemma lem3571394 {A : Type'} (P : A -> Prop) (Q : Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3571395 {_91560 _91563 : Type'} (P : type572 _91560 _91563) (Q : Prop) : (term141 _91560 _91563 P Q) = (term142 _91560 _91563 P Q).
Proof. exact (@lem3571394 (_91560 -> _91563) P Q). Qed.
Lemma lem3571396 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term143 _91560 _91563 f) = (term144 _91560 _91563 f).
Proof. exact (@lem3571395 _91560 _91563 (term46 _91560 _91563 f) (term137 _91560 _91563 f)). Qed.
Lemma lem3571397 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) : (term82 _91560 _91563 f x) = (term45 _91560 _91563 f x).
Proof. exact (eq_refl (term82 _91560 _91563 f x)). Qed.
Lemma lem3571398 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term145 _91560 _91563 f) = (term46 _91560 _91563 f).
Proof. exact (fun_ext (fun x : _91560 -> _91563 => @lem3571397 _91560 _91563 f x)). Qed.
Lemma lem3571399 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571400 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term146 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571399 _91560 _91563) (@lem3571398 _91560 _91563 f)). Qed.
Lemma lem3571401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571402 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term147 _91560 _91563 f) = (term114 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571401) (@lem3571400 _91560 _91563 f)). Qed.
Lemma lem3571403 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term137 _91560 _91563 f) = (term137 _91560 _91563 f).
Proof. exact (eq_refl (term137 _91560 _91563 f)). Qed.
Lemma lem3571404 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term143 _91560 _91563 f) = (term138 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571402 _91560 _91563 f) (@lem3571403 _91560 _91563 f)). Qed.
Lemma lem3571405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571406 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term148 _91560 _91563 f) = (term149 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571405) (@lem3571404 _91560 _91563 f)). Qed.
Lemma lem3571407 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) : (term82 _91560 _91563 f x) = (term45 _91560 _91563 f x).
Proof. exact (eq_refl (term82 _91560 _91563 f x)). Qed.
Lemma lem3571408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571409 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) : (term150 _91560 _91563 f x) = (term151 _91560 _91563 f x).
Proof. exact (MK_COMB (@lem3571408) (@lem3571407 _91560 _91563 f x)). Qed.
Lemma lem3571410 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term137 _91560 _91563 f) = (term137 _91560 _91563 f).
Proof. exact (eq_refl (term137 _91560 _91563 f)). Qed.
Lemma lem3571411 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term152 _91560 _91563 x f) = (term153 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571409 _91560 _91563 f x) (@lem3571410 _91560 _91563 f)). Qed.
Lemma lem3571412 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term154 _91560 _91563 f) = (term155 _91560 _91563 f).
Proof. exact (fun_ext (fun x : _91560 -> _91563 => @lem3571411 _91560 _91563 x f)). Qed.
Lemma lem3571413 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571414 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term144 _91560 _91563 f) = (term156 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571413 _91560 _91563) (@lem3571412 _91560 _91563 f)). Qed.
Lemma lem3571415 {_91560 _91563 : Type'} (f : _91563 -> _91560) : ((term143 _91560 _91563 f) = (term144 _91560 _91563 f)) = ((term138 _91560 _91563 f) = (term156 _91560 _91563 f)).
Proof. exact (MK_COMB (@lem3571406 _91560 _91563 f) (@lem3571414 _91560 _91563 f)). Qed.
Lemma lem3571416 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term138 _91560 _91563 f) = (term156 _91560 _91563 f).
Proof. exact (EQ_MP (@lem3571415 _91560 _91563 f) (@lem3571396 _91560 _91563 f)). Qed.
Lemma lem3571418 {A : Type'} (P : Prop) (Q : A -> Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3571419 {_91560 _91563 : Type'} (P : Prop) (Q : type118 _91560 _91563) : (term159 _91560 _91563 P Q) = (term160 _91560 _91563 P Q).
Proof. exact (@lem3571418 (type569 _91560 _91563) P Q). Qed.
Lemma lem3571420 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term161 _91560 _91563 x f) = (term162 _91560 _91563 x f).
Proof. exact (@lem3571419 _91560 _91563 (term45 _91560 _91563 f x) (term136 _91560 _91563 f)). Qed.
Lemma lem3571421 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term163 _91560 _91563 f y) = (term134 _91560 _91563 f y).
Proof. exact (eq_refl (term163 _91560 _91563 f y)). Qed.
Lemma lem3571422 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term164 _91560 _91563 f) = (term136 _91560 _91563 f).
Proof. exact (fun_ext (fun y : type569 _91560 _91563 => @lem3571421 _91560 _91563 f y)). Qed.
Lemma lem3571423 {_91560 _91563 : Type'} : (@ex ((_91560 -> _91563) -> _91560)) = (@ex ((_91560 -> _91563) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91563) -> _91560))). Qed.
Lemma lem3571424 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term165 _91560 _91563 f) = (term137 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571423 _91560 _91563) (@lem3571422 _91560 _91563 f)). Qed.
Lemma lem3571425 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) : (term151 _91560 _91563 f x) = (term151 _91560 _91563 f x).
Proof. exact (eq_refl (term151 _91560 _91563 f x)). Qed.
Lemma lem3571426 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term161 _91560 _91563 x f) = (term153 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571425 _91560 _91563 f x) (@lem3571424 _91560 _91563 f)). Qed.
Lemma lem3571427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571428 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term166 _91560 _91563 x f) = (term167 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571427) (@lem3571426 _91560 _91563 x f)). Qed.
Lemma lem3571429 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term163 _91560 _91563 f y) = (term134 _91560 _91563 f y).
Proof. exact (eq_refl (term163 _91560 _91563 f y)). Qed.
Lemma lem3571430 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91560 -> _91563) : (term151 _91560 _91563 f x) = (term151 _91560 _91563 f x).
Proof. exact (eq_refl (term151 _91560 _91563 f x)). Qed.
Lemma lem3571431 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term168 _91560 _91563 x f y) = (term169 _91560 _91563 x f y).
Proof. exact (MK_COMB (@lem3571430 _91560 _91563 f x) (@lem3571429 _91560 _91563 f y)). Qed.
Lemma lem3571432 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term170 _91560 _91563 x f) = (term171 _91560 _91563 x f).
Proof. exact (fun_ext (fun y : type569 _91560 _91563 => @lem3571431 _91560 _91563 x f y)). Qed.
Lemma lem3571433 {_91560 _91563 : Type'} : (@ex ((_91560 -> _91563) -> _91560)) = (@ex ((_91560 -> _91563) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91563) -> _91560))). Qed.
Lemma lem3571434 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term162 _91560 _91563 x f) = (term172 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571433 _91560 _91563) (@lem3571432 _91560 _91563 x f)). Qed.
Lemma lem3571435 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : ((term161 _91560 _91563 x f) = (term162 _91560 _91563 x f)) = ((term153 _91560 _91563 x f) = (term172 _91560 _91563 x f)).
Proof. exact (MK_COMB (@lem3571428 _91560 _91563 x f) (@lem3571434 _91560 _91563 x f)). Qed.
Lemma lem3571436 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term153 _91560 _91563 x f) = (term172 _91560 _91563 x f).
Proof. exact (EQ_MP (@lem3571435 _91560 _91563 x f) (@lem3571420 _91560 _91563 x f)). Qed.
Lemma lem3571437 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term155 _91560 _91563 f) = (term173 _91560 _91563 f).
Proof. exact (fun_ext (fun x : _91560 -> _91563 => @lem3571436 _91560 _91563 x f)). Qed.
Lemma lem3571438 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571439 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term156 _91560 _91563 f) = (term174 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571438 _91560 _91563) (@lem3571437 _91560 _91563 f)). Qed.
Lemma lem3571440 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term138 _91560 _91563 f) = (term174 _91560 _91563 f).
Proof. exact (TRANS (@lem3571416 _91560 _91563 f) (@lem3571439 _91560 _91563 f)). Qed.
Lemma lem3571441 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term93 _91560 _91563 f) = (term174 _91560 _91563 f).
Proof. exact (TRANS (@lem3571392 _91560 _91563 f) (@lem3571440 _91560 _91563 f)). Qed.
Lemma lem3571442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3571443 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term95 _91560 _91563 f) = (term175 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571442) (@lem3571441 _91560 _91563 f)). Qed.
Lemma lem3571445 {A : Type'} (P : A -> Prop) (Q : Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3571446 {_91560 : Type'} (P : _91560 -> Prop) (Q : Prop) : (term139 _91560 P Q) = (term140 _91560 P Q).
Proof. exact (@lem3571445 _91560 P Q). Qed.
Lemma lem3571447 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term176 _91560 _91563 f) = (term177 _91560 _91563 f).
Proof. exact (@lem3571446 _91560 (term68 _91560 _91563 f) (term3 _91560 _91563 f)). Qed.
Lemma lem3571448 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term178 _91560 _91563 f y) = (term60 _91560 _91563 f y).
Proof. exact (eq_refl (term178 _91560 _91563 f y)). Qed.
Lemma lem3571449 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term179 _91560 _91563 f) = (term68 _91560 _91563 f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571448 _91560 _91563 f y)). Qed.
Lemma lem3571450 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571451 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term180 _91560 _91563 f) = (term69 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571450 _91560) (@lem3571449 _91560 _91563 f)). Qed.
Lemma lem3571452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571453 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term181 _91560 _91563 f) = (term88 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571452) (@lem3571451 _91560 _91563 f)). Qed.
Lemma lem3571454 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term3 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (eq_refl (term3 _91560 _91563 f)). Qed.
Lemma lem3571455 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term176 _91560 _91563 f) = (term90 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571453 _91560 _91563 f) (@lem3571454 _91560 _91563 f)). Qed.
Lemma lem3571456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571457 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term182 _91560 _91563 f) = (term183 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571456) (@lem3571455 _91560 _91563 f)). Qed.
Lemma lem3571458 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term178 _91560 _91563 f y) = (term60 _91560 _91563 f y).
Proof. exact (eq_refl (term178 _91560 _91563 f y)). Qed.
Lemma lem3571459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571460 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term184 _91560 _91563 f y) = (term185 _91560 _91563 f y).
Proof. exact (MK_COMB (@lem3571459) (@lem3571458 _91560 _91563 f y)). Qed.
Lemma lem3571461 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term3 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (eq_refl (term3 _91560 _91563 f)). Qed.
Lemma lem3571462 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term186 _91560 _91563 y f) = (term187 _91560 _91563 y f).
Proof. exact (MK_COMB (@lem3571460 _91560 _91563 f y) (@lem3571461 _91560 _91563 f)). Qed.
Lemma lem3571463 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term188 _91560 _91563 f) = (term189 _91560 _91563 f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571462 _91560 _91563 y f)). Qed.
Lemma lem3571464 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571465 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term177 _91560 _91563 f) = (term190 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571464 _91560) (@lem3571463 _91560 _91563 f)). Qed.
Lemma lem3571466 {_91560 _91563 : Type'} (f : _91563 -> _91560) : ((term176 _91560 _91563 f) = (term177 _91560 _91563 f)) = ((term90 _91560 _91563 f) = (term190 _91560 _91563 f)).
Proof. exact (MK_COMB (@lem3571457 _91560 _91563 f) (@lem3571465 _91560 _91563 f)). Qed.
Lemma lem3571467 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term90 _91560 _91563 f) = (term190 _91560 _91563 f).
Proof. exact (EQ_MP (@lem3571466 _91560 _91563 f) (@lem3571447 _91560 _91563 f)). Qed.
Lemma lem3571469 {A : Type'} (P : Prop) (Q : A -> Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3571470 {_91560 _91563 : Type'} (P : Prop) (Q : type572 _91560 _91563) : (term191 _91560 _91563 P Q) = (term192 _91560 _91563 P Q).
Proof. exact (@lem3571469 (_91560 -> _91563) P Q). Qed.
Lemma lem3571471 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term193 _91560 _91563 y f) = (term194 _91560 _91563 y f).
Proof. exact (@lem3571470 _91560 _91563 (term60 _91560 _91563 f y) (term46 _91560 _91563 f)). Qed.
Lemma lem3571472 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term82 _91560 _91563 f g) = (term45 _91560 _91563 f g).
Proof. exact (eq_refl (term82 _91560 _91563 f g)). Qed.
Lemma lem3571473 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term145 _91560 _91563 f) = (term46 _91560 _91563 f).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571472 _91560 _91563 f g)). Qed.
Lemma lem3571474 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571475 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term146 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571474 _91560 _91563) (@lem3571473 _91560 _91563 f)). Qed.
Lemma lem3571476 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term185 _91560 _91563 f y) = (term185 _91560 _91563 f y).
Proof. exact (eq_refl (term185 _91560 _91563 f y)). Qed.
Lemma lem3571477 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term193 _91560 _91563 y f) = (term187 _91560 _91563 y f).
Proof. exact (MK_COMB (@lem3571476 _91560 _91563 f y) (@lem3571475 _91560 _91563 f)). Qed.
Lemma lem3571478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571479 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term195 _91560 _91563 y f) = (term196 _91560 _91563 y f).
Proof. exact (MK_COMB (@lem3571478) (@lem3571477 _91560 _91563 y f)). Qed.
Lemma lem3571480 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g : _91560 -> _91563) : (term82 _91560 _91563 f g) = (term45 _91560 _91563 f g).
Proof. exact (eq_refl (term82 _91560 _91563 f g)). Qed.
Lemma lem3571481 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y : _91560) : (term185 _91560 _91563 f y) = (term185 _91560 _91563 f y).
Proof. exact (eq_refl (term185 _91560 _91563 f y)). Qed.
Lemma lem3571482 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) (g : _91560 -> _91563) : (term197 _91560 _91563 y f g) = (term198 _91560 _91563 y f g).
Proof. exact (MK_COMB (@lem3571481 _91560 _91563 f y) (@lem3571480 _91560 _91563 f g)). Qed.
Lemma lem3571483 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term199 _91560 _91563 y f) = (term200 _91560 _91563 y f).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571482 _91560 _91563 y f g)). Qed.
Lemma lem3571484 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571485 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term194 _91560 _91563 y f) = (term201 _91560 _91563 y f).
Proof. exact (MK_COMB (@lem3571484 _91560 _91563) (@lem3571483 _91560 _91563 y f)). Qed.
Lemma lem3571486 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : ((term193 _91560 _91563 y f) = (term194 _91560 _91563 y f)) = ((term187 _91560 _91563 y f) = (term201 _91560 _91563 y f)).
Proof. exact (MK_COMB (@lem3571479 _91560 _91563 y f) (@lem3571485 _91560 _91563 y f)). Qed.
Lemma lem3571487 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term187 _91560 _91563 y f) = (term201 _91560 _91563 y f).
Proof. exact (EQ_MP (@lem3571486 _91560 _91563 y f) (@lem3571471 _91560 _91563 y f)). Qed.
Lemma lem3571488 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term189 _91560 _91563 f) = (term202 _91560 _91563 f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571487 _91560 _91563 y f)). Qed.
Lemma lem3571489 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571490 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term190 _91560 _91563 f) = (term203 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571489 _91560) (@lem3571488 _91560 _91563 f)). Qed.
Lemma lem3571491 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term90 _91560 _91563 f) = (term203 _91560 _91563 f).
Proof. exact (TRANS (@lem3571467 _91560 _91563 f) (@lem3571490 _91560 _91563 f)). Qed.
Lemma lem3571492 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term97 _91560 _91563 f) = (term204 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571443 _91560 _91563 f) (@lem3571491 _91560 _91563 f)). Qed.
Lemma lem3571496 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3571497 {_91560 _91563 : Type'} (P : type572 _91560 _91563) (Q : Prop) : (term207 _91560 _91563 P Q) = (term208 _91560 _91563 P Q).
Proof. exact (@lem3571496 (_91560 -> _91563) P Q). Qed.
Lemma lem3571498 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term209 _91560 _91563 f) = (term210 _91560 _91563 f).
Proof. exact (@lem3571497 _91560 _91563 (term173 _91560 _91563 f) (term203 _91560 _91563 f)). Qed.
Lemma lem3571499 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term211 _91560 _91563 f x) = (term172 _91560 _91563 x f).
Proof. exact (eq_refl (term211 _91560 _91563 f x)). Qed.
Lemma lem3571500 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term212 _91560 _91563 f) = (term173 _91560 _91563 f).
Proof. exact (fun_ext (fun x : _91560 -> _91563 => @lem3571499 _91560 _91563 x f)). Qed.
Lemma lem3571501 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571502 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term213 _91560 _91563 f) = (term174 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571501 _91560 _91563) (@lem3571500 _91560 _91563 f)). Qed.
Lemma lem3571503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3571504 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term214 _91560 _91563 f) = (term175 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571503) (@lem3571502 _91560 _91563 f)). Qed.
Lemma lem3571505 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term203 _91560 _91563 f) = (term203 _91560 _91563 f).
Proof. exact (eq_refl (term203 _91560 _91563 f)). Qed.
Lemma lem3571506 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term209 _91560 _91563 f) = (term204 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571504 _91560 _91563 f) (@lem3571505 _91560 _91563 f)). Qed.
Lemma lem3571507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571508 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term215 _91560 _91563 f) = (term216 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571507) (@lem3571506 _91560 _91563 f)). Qed.
Lemma lem3571509 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term211 _91560 _91563 f x) = (term172 _91560 _91563 x f).
Proof. exact (eq_refl (term211 _91560 _91563 f x)). Qed.
Lemma lem3571510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3571511 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term217 _91560 _91563 f x) = (term218 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571510) (@lem3571509 _91560 _91563 x f)). Qed.
Lemma lem3571512 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term203 _91560 _91563 f) = (term203 _91560 _91563 f).
Proof. exact (eq_refl (term203 _91560 _91563 f)). Qed.
Lemma lem3571513 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term219 _91560 _91563 x f) = (term220 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571511 _91560 _91563 x f) (@lem3571512 _91560 _91563 f)). Qed.
Lemma lem3571514 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term221 _91560 _91563 f) = (term222 _91560 _91563 f).
Proof. exact (fun_ext (fun x : _91560 -> _91563 => @lem3571513 _91560 _91563 x f)). Qed.
Lemma lem3571515 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571516 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term210 _91560 _91563 f) = (term223 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571515 _91560 _91563) (@lem3571514 _91560 _91563 f)). Qed.
Lemma lem3571517 {_91560 _91563 : Type'} (f : _91563 -> _91560) : ((term209 _91560 _91563 f) = (term210 _91560 _91563 f)) = ((term204 _91560 _91563 f) = (term223 _91560 _91563 f)).
Proof. exact (MK_COMB (@lem3571508 _91560 _91563 f) (@lem3571516 _91560 _91563 f)). Qed.
Lemma lem3571518 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term204 _91560 _91563 f) = (term223 _91560 _91563 f).
Proof. exact (EQ_MP (@lem3571517 _91560 _91563 f) (@lem3571498 _91560 _91563 f)). Qed.
Lemma lem3571522 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3571523 {_91560 _91563 : Type'} (P : type118 _91560 _91563) (Q : Prop) : (term224 _91560 _91563 P Q) = (term225 _91560 _91563 P Q).
Proof. exact (@lem3571522 (type569 _91560 _91563) P Q). Qed.
Lemma lem3571524 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term226 _91560 _91563 x f) = (term227 _91560 _91563 x f).
Proof. exact (@lem3571523 _91560 _91563 (term171 _91560 _91563 x f) (term203 _91560 _91563 f)). Qed.
Lemma lem3571525 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term228 _91560 _91563 x f y) = (term169 _91560 _91563 x f y).
Proof. exact (eq_refl (term228 _91560 _91563 x f y)). Qed.
Lemma lem3571526 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term229 _91560 _91563 x f) = (term171 _91560 _91563 x f).
Proof. exact (fun_ext (fun y : type569 _91560 _91563 => @lem3571525 _91560 _91563 x f y)). Qed.
Lemma lem3571527 {_91560 _91563 : Type'} : (@ex ((_91560 -> _91563) -> _91560)) = (@ex ((_91560 -> _91563) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91563) -> _91560))). Qed.
Lemma lem3571528 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term230 _91560 _91563 x f) = (term172 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571527 _91560 _91563) (@lem3571526 _91560 _91563 x f)). Qed.
Lemma lem3571529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3571530 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term231 _91560 _91563 x f) = (term218 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571529) (@lem3571528 _91560 _91563 x f)). Qed.
Lemma lem3571531 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term203 _91560 _91563 f) = (term203 _91560 _91563 f).
Proof. exact (eq_refl (term203 _91560 _91563 f)). Qed.
Lemma lem3571532 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term226 _91560 _91563 x f) = (term220 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571530 _91560 _91563 x f) (@lem3571531 _91560 _91563 f)). Qed.
Lemma lem3571533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571534 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term232 _91560 _91563 x f) = (term233 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571533) (@lem3571532 _91560 _91563 x f)). Qed.
Lemma lem3571535 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term228 _91560 _91563 x f y) = (term169 _91560 _91563 x f y).
Proof. exact (eq_refl (term228 _91560 _91563 x f y)). Qed.
Lemma lem3571536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3571537 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term234 _91560 _91563 x f y) = (term235 _91560 _91563 x f y).
Proof. exact (MK_COMB (@lem3571536) (@lem3571535 _91560 _91563 x f y)). Qed.
Lemma lem3571538 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term203 _91560 _91563 f) = (term203 _91560 _91563 f).
Proof. exact (eq_refl (term203 _91560 _91563 f)). Qed.
Lemma lem3571539 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term236 _91560 _91563 x y f) = (term237 _91560 _91563 x y f).
Proof. exact (MK_COMB (@lem3571537 _91560 _91563 x f y) (@lem3571538 _91560 _91563 f)). Qed.
Lemma lem3571540 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term238 _91560 _91563 x f) = (term239 _91560 _91563 x f).
Proof. exact (fun_ext (fun y : type569 _91560 _91563 => @lem3571539 _91560 _91563 x y f)). Qed.
Lemma lem3571541 {_91560 _91563 : Type'} : (@ex ((_91560 -> _91563) -> _91560)) = (@ex ((_91560 -> _91563) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91563) -> _91560))). Qed.
Lemma lem3571542 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term227 _91560 _91563 x f) = (term240 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571541 _91560 _91563) (@lem3571540 _91560 _91563 x f)). Qed.
Lemma lem3571543 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : ((term226 _91560 _91563 x f) = (term227 _91560 _91563 x f)) = ((term220 _91560 _91563 x f) = (term240 _91560 _91563 x f)).
Proof. exact (MK_COMB (@lem3571534 _91560 _91563 x f) (@lem3571542 _91560 _91563 x f)). Qed.
Lemma lem3571544 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term220 _91560 _91563 x f) = (term240 _91560 _91563 x f).
Proof. exact (EQ_MP (@lem3571543 _91560 _91563 x f) (@lem3571524 _91560 _91563 x f)). Qed.
Lemma lem3571546 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3571547 {_91560 : Type'} (P : Prop) (Q : _91560 -> Prop) : (term241 _91560 P Q) = (term242 _91560 P Q).
Proof. exact (@lem3571546 _91560 P Q). Qed.
Lemma lem3571548 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term243 _91560 _91563 x y f) = (term244 _91560 _91563 x y f).
Proof. exact (@lem3571547 _91560 (term169 _91560 _91563 x f y) (term202 _91560 _91563 f)). Qed.
Lemma lem3571549 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term245 _91560 _91563 f y) = (term201 _91560 _91563 y f).
Proof. exact (eq_refl (term245 _91560 _91563 f y)). Qed.
Lemma lem3571550 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term246 _91560 _91563 f) = (term202 _91560 _91563 f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571549 _91560 _91563 y f)). Qed.
Lemma lem3571551 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571552 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term247 _91560 _91563 f) = (term203 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571551 _91560) (@lem3571550 _91560 _91563 f)). Qed.
Lemma lem3571553 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term235 _91560 _91563 x f y) = (term235 _91560 _91563 x f y).
Proof. exact (eq_refl (term235 _91560 _91563 x f y)). Qed.
Lemma lem3571554 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term243 _91560 _91563 x y f) = (term237 _91560 _91563 x y f).
Proof. exact (MK_COMB (@lem3571553 _91560 _91563 x f y) (@lem3571552 _91560 _91563 f)). Qed.
Lemma lem3571555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571556 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term248 _91560 _91563 x y f) = (term249 _91560 _91563 x y f).
Proof. exact (MK_COMB (@lem3571555) (@lem3571554 _91560 _91563 x y f)). Qed.
Lemma lem3571557 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term245 _91560 _91563 f y) = (term201 _91560 _91563 y f).
Proof. exact (eq_refl (term245 _91560 _91563 f y)). Qed.
Lemma lem3571558 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term235 _91560 _91563 x f y) = (term235 _91560 _91563 x f y).
Proof. exact (eq_refl (term235 _91560 _91563 x f y)). Qed.
Lemma lem3571559 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) : (term250 _91560 _91563 x y f y') = (term251 _91560 _91563 x y y' f).
Proof. exact (MK_COMB (@lem3571558 _91560 _91563 x f y) (@lem3571557 _91560 _91563 y' f)). Qed.
Lemma lem3571560 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term252 _91560 _91563 x y f) = (term253 _91560 _91563 x y f).
Proof. exact (fun_ext (fun y' : _91560 => @lem3571559 _91560 _91563 x y y' f)). Qed.
Lemma lem3571561 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571562 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term244 _91560 _91563 x y f) = (term254 _91560 _91563 x y f).
Proof. exact (MK_COMB (@lem3571561 _91560) (@lem3571560 _91560 _91563 x y f)). Qed.
Lemma lem3571563 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : ((term243 _91560 _91563 x y f) = (term244 _91560 _91563 x y f)) = ((term237 _91560 _91563 x y f) = (term254 _91560 _91563 x y f)).
Proof. exact (MK_COMB (@lem3571556 _91560 _91563 x y f) (@lem3571562 _91560 _91563 x y f)). Qed.
Lemma lem3571564 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term237 _91560 _91563 x y f) = (term254 _91560 _91563 x y f).
Proof. exact (EQ_MP (@lem3571563 _91560 _91563 x y f) (@lem3571548 _91560 _91563 x y f)). Qed.
Lemma lem3571566 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3571567 {_91560 _91563 : Type'} (P : Prop) (Q : type572 _91560 _91563) : (term255 _91560 _91563 P Q) = (term256 _91560 _91563 P Q).
Proof. exact (@lem3571566 (_91560 -> _91563) P Q). Qed.
Lemma lem3571568 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) : (term257 _91560 _91563 x y y' f) = (term258 _91560 _91563 x y y' f).
Proof. exact (@lem3571567 _91560 _91563 (term169 _91560 _91563 x f y) (term200 _91560 _91563 y' f)). Qed.
Lemma lem3571569 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) (g : _91560 -> _91563) : (term259 _91560 _91563 y f g) = (term198 _91560 _91563 y f g).
Proof. exact (eq_refl (term259 _91560 _91563 y f g)). Qed.
Lemma lem3571570 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term260 _91560 _91563 y f) = (term200 _91560 _91563 y f).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571569 _91560 _91563 y f g)). Qed.
Lemma lem3571571 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571572 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) : (term261 _91560 _91563 y f) = (term201 _91560 _91563 y f).
Proof. exact (MK_COMB (@lem3571571 _91560 _91563) (@lem3571570 _91560 _91563 y f)). Qed.
Lemma lem3571573 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term235 _91560 _91563 x f y) = (term235 _91560 _91563 x f y).
Proof. exact (eq_refl (term235 _91560 _91563 x f y)). Qed.
Lemma lem3571574 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) : (term257 _91560 _91563 x y y' f) = (term251 _91560 _91563 x y y' f).
Proof. exact (MK_COMB (@lem3571573 _91560 _91563 x f y) (@lem3571572 _91560 _91563 y' f)). Qed.
Lemma lem3571575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571576 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) : (term262 _91560 _91563 x y y' f) = (term263 _91560 _91563 x y y' f).
Proof. exact (MK_COMB (@lem3571575) (@lem3571574 _91560 _91563 x y y' f)). Qed.
Lemma lem3571577 {_91560 _91563 : Type'} (y : _91560) (f : _91563 -> _91560) (g : _91560 -> _91563) : (term259 _91560 _91563 y f g) = (term198 _91560 _91563 y f g).
Proof. exact (eq_refl (term259 _91560 _91563 y f g)). Qed.
Lemma lem3571578 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) (y : type569 _91560 _91563) : (term235 _91560 _91563 x f y) = (term235 _91560 _91563 x f y).
Proof. exact (eq_refl (term235 _91560 _91563 x f y)). Qed.
Lemma lem3571579 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) (g : _91560 -> _91563) : (term264 _91560 _91563 x y y' f g) = (term265 _91560 _91563 x y y' f g).
Proof. exact (MK_COMB (@lem3571578 _91560 _91563 x f y) (@lem3571577 _91560 _91563 y' f g)). Qed.
Lemma lem3571580 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) : (term266 _91560 _91563 x y y' f) = (term267 _91560 _91563 x y y' f).
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3571579 _91560 _91563 x y y' f g)). Qed.
Lemma lem3571581 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571582 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) : (term258 _91560 _91563 x y y' f) = (term268 _91560 _91563 x y y' f).
Proof. exact (MK_COMB (@lem3571581 _91560 _91563) (@lem3571580 _91560 _91563 x y y' f)). Qed.
Lemma lem3571583 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) : ((term257 _91560 _91563 x y y' f) = (term258 _91560 _91563 x y y' f)) = ((term251 _91560 _91563 x y y' f) = (term268 _91560 _91563 x y y' f)).
Proof. exact (MK_COMB (@lem3571576 _91560 _91563 x y y' f) (@lem3571582 _91560 _91563 x y y' f)). Qed.
Lemma lem3571584 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (y' : _91560) (f : _91563 -> _91560) : (term251 _91560 _91563 x y y' f) = (term268 _91560 _91563 x y y' f).
Proof. exact (EQ_MP (@lem3571583 _91560 _91563 x y y' f) (@lem3571568 _91560 _91563 x y y' f)). Qed.
Lemma lem3571585 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term253 _91560 _91563 x y f) = (term269 _91560 _91563 x y f).
Proof. exact (fun_ext (fun y' : _91560 => @lem3571584 _91560 _91563 x y y' f)). Qed.
Lemma lem3571586 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571587 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term254 _91560 _91563 x y f) = (term270 _91560 _91563 x y f).
Proof. exact (MK_COMB (@lem3571586 _91560) (@lem3571585 _91560 _91563 x y f)). Qed.
Lemma lem3571588 {_91560 _91563 : Type'} (x : _91560 -> _91563) (y : type569 _91560 _91563) (f : _91563 -> _91560) : (term237 _91560 _91563 x y f) = (term270 _91560 _91563 x y f).
Proof. exact (TRANS (@lem3571564 _91560 _91563 x y f) (@lem3571587 _91560 _91563 x y f)). Qed.
Lemma lem3571589 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term239 _91560 _91563 x f) = (term271 _91560 _91563 x f).
Proof. exact (fun_ext (fun y : type569 _91560 _91563 => @lem3571588 _91560 _91563 x y f)). Qed.
Lemma lem3571590 {_91560 _91563 : Type'} : (@ex ((_91560 -> _91563) -> _91560)) = (@ex ((_91560 -> _91563) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91563) -> _91560))). Qed.
Lemma lem3571591 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term240 _91560 _91563 x f) = (term272 _91560 _91563 x f).
Proof. exact (MK_COMB (@lem3571590 _91560 _91563) (@lem3571589 _91560 _91563 x f)). Qed.
Lemma lem3571592 {_91560 _91563 : Type'} (x : _91560 -> _91563) (f : _91563 -> _91560) : (term220 _91560 _91563 x f) = (term272 _91560 _91563 x f).
Proof. exact (TRANS (@lem3571544 _91560 _91563 x f) (@lem3571591 _91560 _91563 x f)). Qed.
Lemma lem3571593 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term222 _91560 _91563 f) = (term273 _91560 _91563 f).
Proof. exact (fun_ext (fun x : _91560 -> _91563 => @lem3571592 _91560 _91563 x f)). Qed.
Lemma lem3571594 {_91560 _91563 : Type'} : (@ex (_91560 -> _91563)) = (@ex (_91560 -> _91563)).
Proof. exact (eq_refl (@ex (_91560 -> _91563))). Qed.
Lemma lem3571595 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term223 _91560 _91563 f) = (term274 _91560 _91563 f).
Proof. exact (MK_COMB (@lem3571594 _91560 _91563) (@lem3571593 _91560 _91563 f)). Qed.
Lemma lem3571596 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term204 _91560 _91563 f) = (term274 _91560 _91563 f).
Proof. exact (TRANS (@lem3571518 _91560 _91563 f) (@lem3571595 _91560 _91563 f)). Qed.
Lemma lem3571598 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term97 _91560 _91563 f) = (term274 _91560 _91563 f).
Proof. exact (TRANS (@lem3571492 _91560 _91563 f) (@lem3571596 _91560 _91563 f)). Qed.
Lemma lem3571599 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term5 _91560 _91563 f) = (term274 _91560 _91563 f).
Proof. exact (TRANS (@lem3571296 _91560 _91563 f) (@lem3571598 _91560 _91563 f)). Qed.
Lemma lem3571600 {_91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term274 _91560 _91563 f.
Proof. exact (EQ_MP (@lem3571599 _91560 _91563 f) (@lem3571226 _91560 _91563 f h1)). Qed.
Lemma lem3571637 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term275 _91307 _91560 s f x y) = (term276 _91307 _91560 s f x y).
Proof. exact (@lem17045 (@IN _91307 x s) ((f x) = y)). Qed.
Lemma lem3571640 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term29 _91307 _91560 s f x y) = (term29 _91307 _91560 s f x y).
Proof. exact (eq_refl (term29 _91307 _91560 s f x y)). Qed.
Lemma lem3571641 {_91307 : Type'} (P : _91307 -> Prop) : (term51 _91307 P) = (term52 _91307 P).
Proof. exact (@lem18394 _91307 P). Qed.
Lemma lem3571642 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term277 _91307 _91560 s f y) = (term278 _91307 _91560 s f y).
Proof. exact (@lem3571641 _91307 (term30 _91307 _91560 s f y)). Qed.
Lemma lem3571643 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term279 _91307 _91560 s f y x) = (term29 _91307 _91560 s f x y).
Proof. exact (eq_refl (term279 _91307 _91560 s f y x)). Qed.
Lemma lem3571644 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571645 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term280 _91307 _91560 s f y x) = (term275 _91307 _91560 s f x y).
Proof. exact (MK_COMB (@lem3571644) (@lem3571643 _91307 _91560 s f x y)). Qed.
Lemma lem3571646 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term280 _91307 _91560 s f y x) = (term276 _91307 _91560 s f x y).
Proof. exact (TRANS (@lem3571645 _91307 _91560 s f x y) (@lem3571637 _91307 _91560 s f x y)). Qed.
Lemma lem3571647 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term281 _91307 _91560 s f y) = (term282 _91307 _91560 s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3571646 _91307 _91560 s f x y)). Qed.
Lemma lem3571648 {_91307 : Type'} : (@all _91307) = (@all _91307).
Proof. exact (eq_refl (@all _91307)). Qed.
Lemma lem3571649 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term278 _91307 _91560 s f y) = (term283 _91307 _91560 s f y).
Proof. exact (MK_COMB (@lem3571648 _91307) (@lem3571647 _91307 _91560 s f y)). Qed.
Lemma lem3571650 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term277 _91307 _91560 s f y) = (term283 _91307 _91560 s f y).
Proof. exact (TRANS (@lem3571642 _91307 _91560 s f y) (@lem3571649 _91307 _91560 s f y)). Qed.
Lemma lem3571651 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term30 _91307 _91560 s f y) = (term30 _91307 _91560 s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3571640 _91307 _91560 s f x y)). Qed.
Lemma lem3571652 {_91307 : Type'} : (@ex _91307) = (@ex _91307).
Proof. exact (eq_refl (@ex _91307)). Qed.
Lemma lem3571653 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term31 _91307 _91560 s f y) = (term31 _91307 _91560 s f y).
Proof. exact (MK_COMB (@lem3571652 _91307) (@lem3571651 _91307 _91560 s f y)). Qed.
Lemma lem3571655 {_91560 : Type'} (y : _91560) (t : _91560 -> Prop) : (term284 _91560 y t) = (term284 _91560 y t).
Proof. exact (eq_refl (term284 _91560 y t)). Qed.
Lemma lem3571656 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term285 _91307 _91560 t s f y) = (term286 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3571655 _91560 y t) (@lem3571650 _91307 _91560 s f y)). Qed.
Lemma lem3571657 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term287 _91307 _91560 t s f y) = (term285 _91307 _91560 t s f y).
Proof. exact (@lem17362 (@IN _91560 y t) (term31 _91307 _91560 s f y)). Qed.
Lemma lem3571658 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term287 _91307 _91560 t s f y) = (term286 _91307 _91560 t s f y).
Proof. exact (TRANS (@lem3571657 _91307 _91560 t s f y) (@lem3571656 _91307 _91560 t s f y)). Qed.
Lemma lem3571660 {_91560 : Type'} (y : _91560) (t : _91560 -> Prop) : (term288 _91560 y t) = (term288 _91560 y t).
Proof. exact (eq_refl (term288 _91560 y t)). Qed.
Lemma lem3571661 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term289 _91307 _91560 t s f y) = (term289 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3571660 _91560 y t) (@lem3571653 _91307 _91560 s f y)). Qed.
Lemma lem3571662 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term33 _91307 _91560 t s f y) = (term289 _91307 _91560 t s f y).
Proof. exact (@lem17265 (@IN _91560 y t) (term31 _91307 _91560 s f y)). Qed.
Lemma lem3571663 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term33 _91307 _91560 t s f y) = (term289 _91307 _91560 t s f y).
Proof. exact (TRANS (@lem3571662 _91307 _91560 t s f y) (@lem3571661 _91307 _91560 t s f y)). Qed.
Lemma lem3571664 {_91560 : Type'} (P : _91560 -> Prop) : (term61 _91560 P) = (term62 _91560 P).
Proof. exact (@lem18392 _91560 P). Qed.
Lemma lem3571665 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term290 _91307 _91560 t s f) = (term291 _91307 _91560 t s f).
Proof. exact (@lem3571664 _91560 (term34 _91307 _91560 t s f)). Qed.
Lemma lem3571666 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term292 _91307 _91560 t s f y) = (term33 _91307 _91560 t s f y).
Proof. exact (eq_refl (term292 _91307 _91560 t s f y)). Qed.
Lemma lem3571667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571668 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term293 _91307 _91560 t s f y) = (term287 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3571667) (@lem3571666 _91307 _91560 t s f y)). Qed.
Lemma lem3571669 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term293 _91307 _91560 t s f y) = (term286 _91307 _91560 t s f y).
Proof. exact (TRANS (@lem3571668 _91307 _91560 t s f y) (@lem3571658 _91307 _91560 t s f y)). Qed.
Lemma lem3571670 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term294 _91307 _91560 t s f) = (term295 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571669 _91307 _91560 t s f y)). Qed.
Lemma lem3571671 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571672 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term291 _91307 _91560 t s f) = (term296 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571671 _91560) (@lem3571670 _91307 _91560 t s f)). Qed.
Lemma lem3571673 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term290 _91307 _91560 t s f) = (term296 _91307 _91560 t s f).
Proof. exact (TRANS (@lem3571665 _91307 _91560 t s f) (@lem3571672 _91307 _91560 t s f)). Qed.
Lemma lem3571674 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term34 _91307 _91560 t s f) = (term297 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3571663 _91307 _91560 t s f y)). Qed.
Lemma lem3571675 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571676 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term35 _91307 _91560 t s f) = (term298 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571675 _91560) (@lem3571674 _91307 _91560 t s f)). Qed.
Lemma lem3571687 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term299 _91307 _91560 s f g y) = (term300 _91307 _91560 s f g y).
Proof. exact (@lem17045 (term301 _91307 _91560 g y s) ((term302 _91307 _91560 f g y) = y)). Qed.
Lemma lem3571692 {_91560 : Type'} (y : _91560) (t : _91560 -> Prop) : (term284 _91560 y t) = (term284 _91560 y t).
Proof. exact (eq_refl (term284 _91560 y t)). Qed.
Lemma lem3571693 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term303 _91307 _91560 t s f g y) = (term304 _91307 _91560 t s f g y).
Proof. exact (MK_COMB (@lem3571692 _91560 y t) (@lem3571687 _91307 _91560 s f g y)). Qed.
Lemma lem3571694 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term305 _91307 _91560 t s f g y) = (term303 _91307 _91560 t s f g y).
Proof. exact (@lem17362 (@IN _91560 y t) (term306 _91307 _91560 s f g y)). Qed.
Lemma lem3571695 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term305 _91307 _91560 t s f g y) = (term304 _91307 _91560 t s f g y).
Proof. exact (TRANS (@lem3571694 _91307 _91560 t s f g y) (@lem3571693 _91307 _91560 t s f g y)). Qed.
Lemma lem3571700 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term24 _91307 _91560 t s f g y) = (term307 _91307 _91560 t s f g y).
Proof. exact (@lem17265 (@IN _91560 y t) (term306 _91307 _91560 s f g y)). Qed.
Lemma lem3571701 {_91560 : Type'} (P : _91560 -> Prop) : (term61 _91560 P) = (term62 _91560 P).
Proof. exact (@lem18392 _91560 P). Qed.
Lemma lem3571702 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term308 _91307 _91560 t s f g) = (term309 _91307 _91560 t s f g).
Proof. exact (@lem3571701 _91560 (term25 _91307 _91560 t s f g)). Qed.
Lemma lem3571703 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term310 _91307 _91560 t s f g y) = (term24 _91307 _91560 t s f g y).
Proof. exact (eq_refl (term310 _91307 _91560 t s f g y)). Qed.
Lemma lem3571704 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571705 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term311 _91307 _91560 t s f g y) = (term305 _91307 _91560 t s f g y).
Proof. exact (MK_COMB (@lem3571704) (@lem3571703 _91307 _91560 t s f g y)). Qed.
Lemma lem3571706 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term311 _91307 _91560 t s f g y) = (term304 _91307 _91560 t s f g y).
Proof. exact (TRANS (@lem3571705 _91307 _91560 t s f g y) (@lem3571695 _91307 _91560 t s f g y)). Qed.
Lemma lem3571707 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term312 _91307 _91560 t s f g) = (term313 _91307 _91560 t s f g).
Proof. exact (fun_ext (fun y : _91560 => @lem3571706 _91307 _91560 t s f g y)). Qed.
Lemma lem3571708 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3571709 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term309 _91307 _91560 t s f g) = (term314 _91307 _91560 t s f g).
Proof. exact (MK_COMB (@lem3571708 _91560) (@lem3571707 _91307 _91560 t s f g)). Qed.
Lemma lem3571710 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term308 _91307 _91560 t s f g) = (term314 _91307 _91560 t s f g).
Proof. exact (TRANS (@lem3571702 _91307 _91560 t s f g) (@lem3571709 _91307 _91560 t s f g)). Qed.
Lemma lem3571711 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term25 _91307 _91560 t s f g) = (term315 _91307 _91560 t s f g).
Proof. exact (fun_ext (fun y : _91560 => @lem3571700 _91307 _91560 t s f g y)). Qed.
Lemma lem3571712 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3571713 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term26 _91307 _91560 t s f g) = (term316 _91307 _91560 t s f g).
Proof. exact (MK_COMB (@lem3571712 _91560) (@lem3571711 _91307 _91560 t s f g)). Qed.
Lemma lem3571714 {_91307 _91560 : Type'} (P : type805 _91307 _91560) : (term317 _91307 _91560 P) = (term318 _91307 _91560 P).
Proof. exact (@lem18394 (_91560 -> _91307) P). Qed.
Lemma lem3571715 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term319 _91307 _91560 t s f) = (term320 _91307 _91560 t s f).
Proof. exact (@lem3571714 _91307 _91560 (term27 _91307 _91560 t s f)). Qed.
Lemma lem3571716 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term321 _91307 _91560 t s f g) = (term26 _91307 _91560 t s f g).
Proof. exact (eq_refl (term321 _91307 _91560 t s f g)). Qed.
Lemma lem3571717 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3571718 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term322 _91307 _91560 t s f g) = (term308 _91307 _91560 t s f g).
Proof. exact (MK_COMB (@lem3571717) (@lem3571716 _91307 _91560 t s f g)). Qed.
Lemma lem3571719 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term322 _91307 _91560 t s f g) = (term314 _91307 _91560 t s f g).
Proof. exact (TRANS (@lem3571718 _91307 _91560 t s f g) (@lem3571710 _91307 _91560 t s f g)). Qed.
Lemma lem3571720 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term323 _91307 _91560 t s f) = (term324 _91307 _91560 t s f).
Proof. exact (fun_ext (fun g : _91560 -> _91307 => @lem3571719 _91307 _91560 t s f g)). Qed.
Lemma lem3571721 {_91307 _91560 : Type'} : (@all (_91560 -> _91307)) = (@all (_91560 -> _91307)).
Proof. exact (eq_refl (@all (_91560 -> _91307))). Qed.
Lemma lem3571722 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term320 _91307 _91560 t s f) = (term325 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571721 _91307 _91560) (@lem3571720 _91307 _91560 t s f)). Qed.
Lemma lem3571723 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term319 _91307 _91560 t s f) = (term325 _91307 _91560 t s f).
Proof. exact (TRANS (@lem3571715 _91307 _91560 t s f) (@lem3571722 _91307 _91560 t s f)). Qed.
Lemma lem3571724 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term27 _91307 _91560 t s f) = (term326 _91307 _91560 t s f).
Proof. exact (fun_ext (fun g : _91560 -> _91307 => @lem3571713 _91307 _91560 t s f g)). Qed.
Lemma lem3571725 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3571726 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term28 _91307 _91560 t s f) = (term327 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571725 _91307 _91560) (@lem3571724 _91307 _91560 t s f)). Qed.
Lemma lem3571727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3571728 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term328 _91307 _91560 t s f) = (term329 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571727) (@lem3571673 _91307 _91560 t s f)). Qed.
Lemma lem3571729 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term330 _91307 _91560 t s f) = (term331 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571728 _91307 _91560 t s f) (@lem3571726 _91307 _91560 t s f)). Qed.
Lemma lem3571730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3571731 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term332 _91307 _91560 t s f) = (term333 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571730) (@lem3571676 _91307 _91560 t s f)). Qed.
Lemma lem3571732 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term334 _91307 _91560 t s f) = (term335 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571731 _91307 _91560 t s f) (@lem3571723 _91307 _91560 t s f)). Qed.
Lemma lem3571733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571734 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term336 _91307 _91560 t s f) = (term337 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571733) (@lem3571732 _91307 _91560 t s f)). Qed.
Lemma lem3571735 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term338 _91307 _91560 t s f) = (term339 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571734 _91307 _91560 t s f) (@lem3571729 _91307 _91560 t s f)). Qed.
Lemma lem3571736 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term35 _91307 _91560 t s f) = (term28 _91307 _91560 t s f)) = (term338 _91307 _91560 t s f).
Proof. exact (@lem17784 (term35 _91307 _91560 t s f) (term28 _91307 _91560 t s f)). Qed.
Lemma lem3571737 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term35 _91307 _91560 t s f) = (term28 _91307 _91560 t s f)) = (term339 _91307 _91560 t s f).
Proof. exact (TRANS (@lem3571736 _91307 _91560 t s f) (@lem3571735 _91307 _91560 t s f)). Qed.
Lemma lem3571738 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term37 _91307 _91560 s f) = (term340 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3571737 _91307 _91560 t s f)). Qed.
Lemma lem3571739 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3571740 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term38 _91307 _91560 s f) = (term341 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3571739 _91560) (@lem3571738 _91307 _91560 s f)). Qed.
Lemma lem3571741 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term39 _91307 _91560 s) = (term342 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3571740 _91307 _91560 s f)). Qed.
Lemma lem3571742 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3571743 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term40 _91307 _91560 s) = (term343 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3571742 _91307 _91560) (@lem3571741 _91307 _91560 s)). Qed.
Lemma lem3571744 {_91307 _91560 : Type'} : (term41 _91307 _91560) = (term344 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3571743 _91307 _91560 s)). Qed.
Lemma lem3571745 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3571746 {_91307 _91560 : Type'} : (term0 _91307 _91560) = (term345 _91307 _91560).
Proof. exact (MK_COMB (@lem3571745 _91307) (@lem3571744 _91307 _91560)). Qed.
Lemma lem3571756 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3571757 {_91560 : Type'} (P : type686 _91560) (Q : type686 _91560) : (term348 _91560 P Q) = (term349 _91560 P Q).
Proof. exact (@lem3571756 (_91560 -> Prop) P Q). Qed.
Lemma lem3571758 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term350 _91307 _91560 s f) = (term351 _91307 _91560 s f).
Proof. exact (@lem3571757 _91560 (term352 _91307 _91560 s f) (term353 _91307 _91560 s f)). Qed.
Lemma lem3571759 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term354 _91307 _91560 s f t) = (term335 _91307 _91560 t s f).
Proof. exact (eq_refl (term354 _91307 _91560 s f t)). Qed.
Lemma lem3571760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571761 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term355 _91307 _91560 s f t) = (term337 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571760) (@lem3571759 _91307 _91560 t s f)). Qed.
Lemma lem3571762 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term356 _91307 _91560 s f t) = (term331 _91307 _91560 t s f).
Proof. exact (eq_refl (term356 _91307 _91560 s f t)). Qed.
Lemma lem3571763 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term357 _91307 _91560 s f t) = (term339 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3571761 _91307 _91560 t s f) (@lem3571762 _91307 _91560 t s f)). Qed.
Lemma lem3571764 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term358 _91307 _91560 s f) = (term340 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3571763 _91307 _91560 t s f)). Qed.
Lemma lem3571765 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3571766 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term350 _91307 _91560 s f) = (term341 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3571765 _91560) (@lem3571764 _91307 _91560 s f)). Qed.
Lemma lem3571767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3571768 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term359 _91307 _91560 s f) = (term360 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3571767) (@lem3571766 _91307 _91560 s f)). Qed.
Lemma lem3571769 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term354 _91307 _91560 s f t) = (term335 _91307 _91560 t s f).
Proof. exact (eq_refl (term354 _91307 _91560 s f t)). Qed.
Lemma lem3571770 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term361 _91307 _91560 s f) = (term352 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3571769 _91307 _91560 t s f)). Qed.
Lemma lem3571771 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3571772 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term362 _91307 _91560 s f) = (term363 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3571771 _91560) (@lem3571770 _91307 _91560 s f)). Qed.
Lemma lem3571773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3571774 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term364 _91307 _91560 s f) = (term365 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3571773) (@lem3571772 _91307 _91560 s f)). Qed.
Lemma lem3571775 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term356 _91307 _91560 s f t) = (term331 _91307 _91560 t s f).
Proof. exact (eq_refl (term356 _91307 _91560 s f t)). Qed.
Lemma lem3571776 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term366 _91307 _91560 s f) = (term353 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3571775 _91307 _91560 t s f)). Qed.
Lemma lem3571777 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3571778 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term367 _91307 _91560 s f) = (term368 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3571777 _91560) (@lem3571776 _91307 _91560 s f)). Qed.
Lemma lem3571779 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term351 _91307 _91560 s f) = (term369 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3571774 _91307 _91560 s f) (@lem3571778 _91307 _91560 s f)). Qed.
Lemma lem3571780 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term350 _91307 _91560 s f) = (term351 _91307 _91560 s f)) = ((term341 _91307 _91560 s f) = (term369 _91307 _91560 s f)).
Proof. exact (MK_COMB (@lem3571768 _91307 _91560 s f) (@lem3571779 _91307 _91560 s f)). Qed.
Lemma lem3571781 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term341 _91307 _91560 s f) = (term369 _91307 _91560 s f).
Proof. exact (EQ_MP (@lem3571780 _91307 _91560 s f) (@lem3571758 _91307 _91560 s f)). Qed.
Lemma lem3572174 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term342 _91307 _91560 s) = (term370 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3571781 _91307 _91560 s f)). Qed.
Lemma lem3572175 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3572176 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term343 _91307 _91560 s) = (term371 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572175 _91307 _91560) (@lem3572174 _91307 _91560 s)). Qed.
Lemma lem3572178 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3572179 {_91307 _91560 : Type'} (P : type572 _91307 _91560) (Q : type572 _91307 _91560) : (term372 _91307 _91560 P Q) = (term373 _91307 _91560 P Q).
Proof. exact (@lem3572178 (_91307 -> _91560) P Q). Qed.
Lemma lem3572180 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term374 _91307 _91560 s) = (term375 _91307 _91560 s).
Proof. exact (@lem3572179 _91307 _91560 (term376 _91307 _91560 s) (term377 _91307 _91560 s)). Qed.
Lemma lem3572181 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term378 _91307 _91560 s f) = (term363 _91307 _91560 s f).
Proof. exact (eq_refl (term378 _91307 _91560 s f)). Qed.
Lemma lem3572182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3572183 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term379 _91307 _91560 s f) = (term365 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3572182) (@lem3572181 _91307 _91560 s f)). Qed.
Lemma lem3572184 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term380 _91307 _91560 s f) = (term368 _91307 _91560 s f).
Proof. exact (eq_refl (term380 _91307 _91560 s f)). Qed.
Lemma lem3572185 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term381 _91307 _91560 s f) = (term369 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3572183 _91307 _91560 s f) (@lem3572184 _91307 _91560 s f)). Qed.
Lemma lem3572186 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term382 _91307 _91560 s) = (term370 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3572185 _91307 _91560 s f)). Qed.
Lemma lem3572187 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3572188 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term374 _91307 _91560 s) = (term371 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572187 _91307 _91560) (@lem3572186 _91307 _91560 s)). Qed.
Lemma lem3572189 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3572190 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term383 _91307 _91560 s) = (term384 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572189) (@lem3572188 _91307 _91560 s)). Qed.
Lemma lem3572191 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term378 _91307 _91560 s f) = (term363 _91307 _91560 s f).
Proof. exact (eq_refl (term378 _91307 _91560 s f)). Qed.
Lemma lem3572192 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term385 _91307 _91560 s) = (term376 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3572191 _91307 _91560 s f)). Qed.
Lemma lem3572193 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3572194 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term386 _91307 _91560 s) = (term387 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572193 _91307 _91560) (@lem3572192 _91307 _91560 s)). Qed.
Lemma lem3572195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3572196 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term388 _91307 _91560 s) = (term389 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572195) (@lem3572194 _91307 _91560 s)). Qed.
Lemma lem3572197 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term380 _91307 _91560 s f) = (term368 _91307 _91560 s f).
Proof. exact (eq_refl (term380 _91307 _91560 s f)). Qed.
Lemma lem3572198 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term390 _91307 _91560 s) = (term377 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3572197 _91307 _91560 s f)). Qed.
Lemma lem3572199 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3572200 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term391 _91307 _91560 s) = (term392 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572199 _91307 _91560) (@lem3572198 _91307 _91560 s)). Qed.
Lemma lem3572201 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term375 _91307 _91560 s) = (term393 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572196 _91307 _91560 s) (@lem3572200 _91307 _91560 s)). Qed.
Lemma lem3572202 {_91307 _91560 : Type'} (s : _91307 -> Prop) : ((term374 _91307 _91560 s) = (term375 _91307 _91560 s)) = ((term371 _91307 _91560 s) = (term393 _91307 _91560 s)).
Proof. exact (MK_COMB (@lem3572190 _91307 _91560 s) (@lem3572201 _91307 _91560 s)). Qed.
Lemma lem3572203 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term371 _91307 _91560 s) = (term393 _91307 _91560 s).
Proof. exact (EQ_MP (@lem3572202 _91307 _91560 s) (@lem3572180 _91307 _91560 s)). Qed.
Lemma lem3572604 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term343 _91307 _91560 s) = (term393 _91307 _91560 s).
Proof. exact (TRANS (@lem3572176 _91307 _91560 s) (@lem3572203 _91307 _91560 s)). Qed.
Lemma lem3572605 {_91307 _91560 : Type'} : (term344 _91307 _91560) = (term394 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3572604 _91307 _91560 s)). Qed.
Lemma lem3572606 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3572607 {_91307 _91560 : Type'} : (term345 _91307 _91560) = (term395 _91307 _91560).
Proof. exact (MK_COMB (@lem3572606 _91307) (@lem3572605 _91307 _91560)). Qed.
Lemma lem3572609 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3572610 {_91307 : Type'} (P : type686 _91307) (Q : type686 _91307) : (term348 _91307 P Q) = (term349 _91307 P Q).
Proof. exact (@lem3572609 (_91307 -> Prop) P Q). Qed.
Lemma lem3572611 {_91307 _91560 : Type'} : (term396 _91307 _91560) = (term397 _91307 _91560).
Proof. exact (@lem3572610 _91307 (term398 _91307 _91560) (term399 _91307 _91560)). Qed.
Lemma lem3572612 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term400 _91307 _91560 s) = (term387 _91307 _91560 s).
Proof. exact (eq_refl (term400 _91307 _91560 s)). Qed.
Lemma lem3572613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3572614 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term401 _91307 _91560 s) = (term389 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572613) (@lem3572612 _91307 _91560 s)). Qed.
Lemma lem3572615 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term402 _91307 _91560 s) = (term392 _91307 _91560 s).
Proof. exact (eq_refl (term402 _91307 _91560 s)). Qed.
Lemma lem3572616 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term403 _91307 _91560 s) = (term393 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3572614 _91307 _91560 s) (@lem3572615 _91307 _91560 s)). Qed.
Lemma lem3572617 {_91307 _91560 : Type'} : (term404 _91307 _91560) = (term394 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3572616 _91307 _91560 s)). Qed.
Lemma lem3572618 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3572619 {_91307 _91560 : Type'} : (term396 _91307 _91560) = (term395 _91307 _91560).
Proof. exact (MK_COMB (@lem3572618 _91307) (@lem3572617 _91307 _91560)). Qed.
Lemma lem3572620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3572621 {_91307 _91560 : Type'} : (term405 _91307 _91560) = (term406 _91307 _91560).
Proof. exact (MK_COMB (@lem3572620) (@lem3572619 _91307 _91560)). Qed.
Lemma lem3572622 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term400 _91307 _91560 s) = (term387 _91307 _91560 s).
Proof. exact (eq_refl (term400 _91307 _91560 s)). Qed.
Lemma lem3572623 {_91307 _91560 : Type'} : (term407 _91307 _91560) = (term398 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3572622 _91307 _91560 s)). Qed.
Lemma lem3572624 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3572625 {_91307 _91560 : Type'} : (term408 _91307 _91560) = (term409 _91307 _91560).
Proof. exact (MK_COMB (@lem3572624 _91307) (@lem3572623 _91307 _91560)). Qed.
Lemma lem3572626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3572627 {_91307 _91560 : Type'} : (term410 _91307 _91560) = (term411 _91307 _91560).
Proof. exact (MK_COMB (@lem3572626) (@lem3572625 _91307 _91560)). Qed.
Lemma lem3572628 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term402 _91307 _91560 s) = (term392 _91307 _91560 s).
Proof. exact (eq_refl (term402 _91307 _91560 s)). Qed.
Lemma lem3572629 {_91307 _91560 : Type'} : (term412 _91307 _91560) = (term399 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3572628 _91307 _91560 s)). Qed.
Lemma lem3572630 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3572631 {_91307 _91560 : Type'} : (term413 _91307 _91560) = (term414 _91307 _91560).
Proof. exact (MK_COMB (@lem3572630 _91307) (@lem3572629 _91307 _91560)). Qed.
Lemma lem3572632 {_91307 _91560 : Type'} : (term397 _91307 _91560) = (term415 _91307 _91560).
Proof. exact (MK_COMB (@lem3572627 _91307 _91560) (@lem3572631 _91307 _91560)). Qed.
Lemma lem3572633 {_91307 _91560 : Type'} : ((term396 _91307 _91560) = (term397 _91307 _91560)) = ((term395 _91307 _91560) = (term415 _91307 _91560)).
Proof. exact (MK_COMB (@lem3572621 _91307 _91560) (@lem3572632 _91307 _91560)). Qed.
Lemma lem3572634 {_91307 _91560 : Type'} : (term395 _91307 _91560) = (term415 _91307 _91560).
Proof. exact (EQ_MP (@lem3572633 _91307 _91560) (@lem3572611 _91307 _91560)). Qed.
Lemma lem3573043 {_91307 _91560 : Type'} : (term345 _91307 _91560) = (term415 _91307 _91560).
Proof. exact (TRANS (@lem3572607 _91307 _91560) (@lem3572634 _91307 _91560)). Qed.
Lemma lem3573045 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3573046 {_91307 : Type'} (P : Prop) (Q : _91307 -> Prop) : (term241 _91307 P Q) = (term242 _91307 P Q).
Proof. exact (@lem3573045 _91307 P Q). Qed.
Lemma lem3573047 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term416 _91307 _91560 t s f y) = (term417 _91307 _91560 t s f y).
Proof. exact (@lem3573046 _91307 (term418 _91560 y t) (term30 _91307 _91560 s f y)). Qed.
Lemma lem3573048 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term279 _91307 _91560 s f y x) = (term29 _91307 _91560 s f x y).
Proof. exact (eq_refl (term279 _91307 _91560 s f y x)). Qed.
Lemma lem3573049 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term419 _91307 _91560 s f y) = (term30 _91307 _91560 s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3573048 _91307 _91560 s f x y)). Qed.
Lemma lem3573050 {_91307 : Type'} : (@ex _91307) = (@ex _91307).
Proof. exact (eq_refl (@ex _91307)). Qed.
Lemma lem3573051 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term420 _91307 _91560 s f y) = (term31 _91307 _91560 s f y).
Proof. exact (MK_COMB (@lem3573050 _91307) (@lem3573049 _91307 _91560 s f y)). Qed.
Lemma lem3573052 {_91560 : Type'} (y : _91560) (t : _91560 -> Prop) : (term288 _91560 y t) = (term288 _91560 y t).
Proof. exact (eq_refl (term288 _91560 y t)). Qed.
Lemma lem3573053 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term416 _91307 _91560 t s f y) = (term289 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3573052 _91560 y t) (@lem3573051 _91307 _91560 s f y)). Qed.
Lemma lem3573054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573055 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term421 _91307 _91560 t s f y) = (term422 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3573054) (@lem3573053 _91307 _91560 t s f y)). Qed.
Lemma lem3573056 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term279 _91307 _91560 s f y x) = (term29 _91307 _91560 s f x y).
Proof. exact (eq_refl (term279 _91307 _91560 s f y x)). Qed.
Lemma lem3573057 {_91560 : Type'} (y : _91560) (t : _91560 -> Prop) : (term288 _91560 y t) = (term288 _91560 y t).
Proof. exact (eq_refl (term288 _91560 y t)). Qed.
Lemma lem3573058 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term423 _91307 _91560 t s f y x) = (term424 _91307 _91560 t s f x y).
Proof. exact (MK_COMB (@lem3573057 _91560 y t) (@lem3573056 _91307 _91560 s f x y)). Qed.
Lemma lem3573059 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term425 _91307 _91560 t s f y) = (term426 _91307 _91560 t s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3573058 _91307 _91560 t s f x y)). Qed.
Lemma lem3573060 {_91307 : Type'} : (@ex _91307) = (@ex _91307).
Proof. exact (eq_refl (@ex _91307)). Qed.
Lemma lem3573061 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term417 _91307 _91560 t s f y) = (term427 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3573060 _91307) (@lem3573059 _91307 _91560 t s f y)). Qed.
Lemma lem3573062 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : ((term416 _91307 _91560 t s f y) = (term417 _91307 _91560 t s f y)) = ((term289 _91307 _91560 t s f y) = (term427 _91307 _91560 t s f y)).
Proof. exact (MK_COMB (@lem3573055 _91307 _91560 t s f y) (@lem3573061 _91307 _91560 t s f y)). Qed.
Lemma lem3573063 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term289 _91307 _91560 t s f y) = (term427 _91307 _91560 t s f y).
Proof. exact (EQ_MP (@lem3573062 _91307 _91560 t s f y) (@lem3573047 _91307 _91560 t s f y)). Qed.
Lemma lem3573064 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term297 _91307 _91560 t s f) = (term428 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3573063 _91307 _91560 t s f y)). Qed.
Lemma lem3573065 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3573066 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term298 _91307 _91560 t s f) = (term429 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573065 _91560) (@lem3573064 _91307 _91560 t s f)). Qed.
Lemma lem3573068 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573069 {_91307 _91560 : Type'} (P : type1470 _91307 _91560) : (term430 _91307 _91560 P) = (term431 _91307 _91560 P).
Proof. exact (@lem3573068 _91560 _91307 P). Qed.
Lemma lem3573070 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term432 _91307 _91560 t s f) = (term433 _91307 _91560 t s f).
Proof. exact (@lem3573069 _91307 _91560 (term434 _91307 _91560 t s f)). Qed.
Lemma lem3573071 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term435 _91307 _91560 t s f y) = (term426 _91307 _91560 t s f y).
Proof. exact (eq_refl (term435 _91307 _91560 t s f y)). Qed.
Lemma lem3573072 {_91307 : Type'} (x : _91307) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3573073 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) (x : _91307) : (term436 _91307 _91560 t s f y x) = (term437 _91307 _91560 t s f y x).
Proof. exact (MK_COMB (@lem3573071 _91307 _91560 t s f y) (@lem3573072 _91307 x)). Qed.
Lemma lem3573074 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term437 _91307 _91560 t s f y x) = (term424 _91307 _91560 t s f x y).
Proof. exact (eq_refl (term437 _91307 _91560 t s f y x)). Qed.
Lemma lem3573075 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91307) (y : _91560) : (term436 _91307 _91560 t s f y x) = (term424 _91307 _91560 t s f x y).
Proof. exact (TRANS (@lem3573073 _91307 _91560 t s f y x) (@lem3573074 _91307 _91560 t s f x y)). Qed.
Lemma lem3573076 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term438 _91307 _91560 t s f y) = (term426 _91307 _91560 t s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3573075 _91307 _91560 t s f x y)). Qed.
Lemma lem3573077 {_91307 : Type'} : (@ex _91307) = (@ex _91307).
Proof. exact (eq_refl (@ex _91307)). Qed.
Lemma lem3573078 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term439 _91307 _91560 t s f y) = (term427 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3573077 _91307) (@lem3573076 _91307 _91560 t s f y)). Qed.
Lemma lem3573079 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term440 _91307 _91560 t s f) = (term428 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3573078 _91307 _91560 t s f y)). Qed.
Lemma lem3573080 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3573081 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term432 _91307 _91560 t s f) = (term429 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573080 _91560) (@lem3573079 _91307 _91560 t s f)). Qed.
Lemma lem3573082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573083 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term441 _91307 _91560 t s f) = (term442 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573082) (@lem3573081 _91307 _91560 t s f)). Qed.
Lemma lem3573084 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term435 _91307 _91560 t s f y) = (term426 _91307 _91560 t s f y).
Proof. exact (eq_refl (term435 _91307 _91560 t s f y)). Qed.
Lemma lem3573085 {_91307 _91560 : Type'} (x : _91560 -> _91307) (y : _91560) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3573086 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) (y : _91560) : (term443 _91307 _91560 t s f x y) = (term444 _91307 _91560 t s f x y).
Proof. exact (MK_COMB (@lem3573084 _91307 _91560 t s f y) (@lem3573085 _91307 _91560 x y)). Qed.
Lemma lem3573087 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) (y : _91560) : (term444 _91307 _91560 t s f x y) = (term307 _91307 _91560 t s f x y).
Proof. exact (eq_refl (term444 _91307 _91560 t s f x y)). Qed.
Lemma lem3573088 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) (y : _91560) : (term443 _91307 _91560 t s f x y) = (term307 _91307 _91560 t s f x y).
Proof. exact (TRANS (@lem3573086 _91307 _91560 t s f x y) (@lem3573087 _91307 _91560 t s f x y)). Qed.
Lemma lem3573089 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) : (term445 _91307 _91560 t s f x) = (term315 _91307 _91560 t s f x).
Proof. exact (fun_ext (fun y : _91560 => @lem3573088 _91307 _91560 t s f x y)). Qed.
Lemma lem3573090 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3573091 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) : (term446 _91307 _91560 t s f x) = (term316 _91307 _91560 t s f x).
Proof. exact (MK_COMB (@lem3573090 _91560) (@lem3573089 _91307 _91560 t s f x)). Qed.
Lemma lem3573092 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term447 _91307 _91560 t s f) = (term326 _91307 _91560 t s f).
Proof. exact (fun_ext (fun x : _91560 -> _91307 => @lem3573091 _91307 _91560 t s f x)). Qed.
Lemma lem3573093 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3573094 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term433 _91307 _91560 t s f) = (term327 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573093 _91307 _91560) (@lem3573092 _91307 _91560 t s f)). Qed.
Lemma lem3573095 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term432 _91307 _91560 t s f) = (term433 _91307 _91560 t s f)) = ((term429 _91307 _91560 t s f) = (term327 _91307 _91560 t s f)).
Proof. exact (MK_COMB (@lem3573083 _91307 _91560 t s f) (@lem3573094 _91307 _91560 t s f)). Qed.
Lemma lem3573096 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term429 _91307 _91560 t s f) = (term327 _91307 _91560 t s f).
Proof. exact (EQ_MP (@lem3573095 _91307 _91560 t s f) (@lem3573070 _91307 _91560 t s f)). Qed.
Lemma lem3573097 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term298 _91307 _91560 t s f) = (term327 _91307 _91560 t s f).
Proof. exact (TRANS (@lem3573066 _91307 _91560 t s f) (@lem3573096 _91307 _91560 t s f)). Qed.
Lemma lem3573098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3573099 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term333 _91307 _91560 t s f) = (term448 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573098) (@lem3573097 _91307 _91560 t s f)). Qed.
Lemma lem3573101 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573102 {_91307 _91560 : Type'} (P : type799 _91307 _91560) : (term449 _91307 _91560 P) = (term450 _91307 _91560 P).
Proof. exact (@lem3573101 (_91560 -> _91307) _91560 P). Qed.
Lemma lem3573103 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term451 _91307 _91560 t s f) = (term452 _91307 _91560 t s f).
Proof. exact (@lem3573102 _91307 _91560 (term453 _91307 _91560 t s f)). Qed.
Lemma lem3573104 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term454 _91307 _91560 t s f g) = (term313 _91307 _91560 t s f g).
Proof. exact (eq_refl (term454 _91307 _91560 t s f g)). Qed.
Lemma lem3573105 {_91560 : Type'} (y : _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3573106 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term455 _91307 _91560 t s f g y) = (term456 _91307 _91560 t s f g y).
Proof. exact (MK_COMB (@lem3573104 _91307 _91560 t s f g) (@lem3573105 _91560 y)). Qed.
Lemma lem3573107 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term456 _91307 _91560 t s f g y) = (term304 _91307 _91560 t s f g y).
Proof. exact (eq_refl (term456 _91307 _91560 t s f g y)). Qed.
Lemma lem3573108 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) (y : _91560) : (term455 _91307 _91560 t s f g y) = (term304 _91307 _91560 t s f g y).
Proof. exact (TRANS (@lem3573106 _91307 _91560 t s f g y) (@lem3573107 _91307 _91560 t s f g y)). Qed.
Lemma lem3573109 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term457 _91307 _91560 t s f g) = (term313 _91307 _91560 t s f g).
Proof. exact (fun_ext (fun y : _91560 => @lem3573108 _91307 _91560 t s f g y)). Qed.
Lemma lem3573110 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3573111 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term458 _91307 _91560 t s f g) = (term314 _91307 _91560 t s f g).
Proof. exact (MK_COMB (@lem3573110 _91560) (@lem3573109 _91307 _91560 t s f g)). Qed.
Lemma lem3573112 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term459 _91307 _91560 t s f) = (term324 _91307 _91560 t s f).
Proof. exact (fun_ext (fun g : _91560 -> _91307 => @lem3573111 _91307 _91560 t s f g)). Qed.
Lemma lem3573113 {_91307 _91560 : Type'} : (@all (_91560 -> _91307)) = (@all (_91560 -> _91307)).
Proof. exact (eq_refl (@all (_91560 -> _91307))). Qed.
Lemma lem3573114 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term451 _91307 _91560 t s f) = (term325 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573113 _91307 _91560) (@lem3573112 _91307 _91560 t s f)). Qed.
Lemma lem3573115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573116 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term460 _91307 _91560 t s f) = (term461 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573115) (@lem3573114 _91307 _91560 t s f)). Qed.
Lemma lem3573117 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term454 _91307 _91560 t s f g) = (term313 _91307 _91560 t s f g).
Proof. exact (eq_refl (term454 _91307 _91560 t s f g)). Qed.
Lemma lem3573118 {_91307 _91560 : Type'} (y : type803 _91307 _91560) (g : _91560 -> _91307) : (y g) = (y g).
Proof. exact (eq_refl (y g)). Qed.
Lemma lem3573119 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) (g : _91560 -> _91307) : (term462 _91307 _91560 t s f y g) = (term463 _91307 _91560 t s f y g).
Proof. exact (MK_COMB (@lem3573117 _91307 _91560 t s f g) (@lem3573118 _91307 _91560 y g)). Qed.
Lemma lem3573120 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) (g : _91560 -> _91307) : (term463 _91307 _91560 t s f y g) = (term464 _91307 _91560 t s f y g).
Proof. exact (eq_refl (term463 _91307 _91560 t s f y g)). Qed.
Lemma lem3573121 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) (g : _91560 -> _91307) : (term462 _91307 _91560 t s f y g) = (term464 _91307 _91560 t s f y g).
Proof. exact (TRANS (@lem3573119 _91307 _91560 t s f y g) (@lem3573120 _91307 _91560 t s f y g)). Qed.
Lemma lem3573122 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) : (term465 _91307 _91560 t s f y) = (term466 _91307 _91560 t s f y).
Proof. exact (fun_ext (fun g : _91560 -> _91307 => @lem3573121 _91307 _91560 t s f y g)). Qed.
Lemma lem3573123 {_91307 _91560 : Type'} : (@all (_91560 -> _91307)) = (@all (_91560 -> _91307)).
Proof. exact (eq_refl (@all (_91560 -> _91307))). Qed.
Lemma lem3573124 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) : (term467 _91307 _91560 t s f y) = (term468 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3573123 _91307 _91560) (@lem3573122 _91307 _91560 t s f y)). Qed.
Lemma lem3573125 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term469 _91307 _91560 t s f) = (term470 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : type803 _91307 _91560 => @lem3573124 _91307 _91560 t s f y)). Qed.
Lemma lem3573126 {_91307 _91560 : Type'} : (@ex ((_91560 -> _91307) -> _91560)) = (@ex ((_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573127 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term452 _91307 _91560 t s f) = (term471 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573126 _91307 _91560) (@lem3573125 _91307 _91560 t s f)). Qed.
Lemma lem3573128 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term451 _91307 _91560 t s f) = (term452 _91307 _91560 t s f)) = ((term325 _91307 _91560 t s f) = (term471 _91307 _91560 t s f)).
Proof. exact (MK_COMB (@lem3573116 _91307 _91560 t s f) (@lem3573127 _91307 _91560 t s f)). Qed.
Lemma lem3573129 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term325 _91307 _91560 t s f) = (term471 _91307 _91560 t s f).
Proof. exact (EQ_MP (@lem3573128 _91307 _91560 t s f) (@lem3573103 _91307 _91560 t s f)). Qed.
Lemma lem3573130 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term335 _91307 _91560 t s f) = (term472 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573099 _91307 _91560 t s f) (@lem3573129 _91307 _91560 t s f)). Qed.
Lemma lem3573134 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3573135 {_91307 _91560 : Type'} (P : type805 _91307 _91560) (Q : Prop) : (term473 _91307 _91560 P Q) = (term474 _91307 _91560 P Q).
Proof. exact (@lem3573134 (_91560 -> _91307) P Q). Qed.
Lemma lem3573136 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term475 _91307 _91560 t s f) = (term476 _91307 _91560 t s f).
Proof. exact (@lem3573135 _91307 _91560 (term326 _91307 _91560 t s f) (term471 _91307 _91560 t s f)). Qed.
Lemma lem3573137 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) : (term477 _91307 _91560 t s f x) = (term316 _91307 _91560 t s f x).
Proof. exact (eq_refl (term477 _91307 _91560 t s f x)). Qed.
Lemma lem3573138 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term478 _91307 _91560 t s f) = (term326 _91307 _91560 t s f).
Proof. exact (fun_ext (fun x : _91560 -> _91307 => @lem3573137 _91307 _91560 t s f x)). Qed.
Lemma lem3573139 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3573140 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term479 _91307 _91560 t s f) = (term327 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573139 _91307 _91560) (@lem3573138 _91307 _91560 t s f)). Qed.
Lemma lem3573141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3573142 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term480 _91307 _91560 t s f) = (term448 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573141) (@lem3573140 _91307 _91560 t s f)). Qed.
Lemma lem3573143 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term471 _91307 _91560 t s f) = (term471 _91307 _91560 t s f).
Proof. exact (eq_refl (term471 _91307 _91560 t s f)). Qed.
Lemma lem3573144 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term475 _91307 _91560 t s f) = (term472 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573142 _91307 _91560 t s f) (@lem3573143 _91307 _91560 t s f)). Qed.
Lemma lem3573145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573146 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term481 _91307 _91560 t s f) = (term482 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573145) (@lem3573144 _91307 _91560 t s f)). Qed.
Lemma lem3573147 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) : (term477 _91307 _91560 t s f x) = (term316 _91307 _91560 t s f x).
Proof. exact (eq_refl (term477 _91307 _91560 t s f x)). Qed.
Lemma lem3573148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3573149 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) : (term483 _91307 _91560 t s f x) = (term484 _91307 _91560 t s f x).
Proof. exact (MK_COMB (@lem3573148) (@lem3573147 _91307 _91560 t s f x)). Qed.
Lemma lem3573150 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term471 _91307 _91560 t s f) = (term471 _91307 _91560 t s f).
Proof. exact (eq_refl (term471 _91307 _91560 t s f)). Qed.
Lemma lem3573151 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term485 _91307 _91560 x t s f) = (term486 _91307 _91560 x t s f).
Proof. exact (MK_COMB (@lem3573149 _91307 _91560 t s f x) (@lem3573150 _91307 _91560 t s f)). Qed.
Lemma lem3573152 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term487 _91307 _91560 t s f) = (term488 _91307 _91560 t s f).
Proof. exact (fun_ext (fun x : _91560 -> _91307 => @lem3573151 _91307 _91560 x t s f)). Qed.
Lemma lem3573153 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3573154 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term476 _91307 _91560 t s f) = (term489 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573153 _91307 _91560) (@lem3573152 _91307 _91560 t s f)). Qed.
Lemma lem3573155 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term475 _91307 _91560 t s f) = (term476 _91307 _91560 t s f)) = ((term472 _91307 _91560 t s f) = (term489 _91307 _91560 t s f)).
Proof. exact (MK_COMB (@lem3573146 _91307 _91560 t s f) (@lem3573154 _91307 _91560 t s f)). Qed.
Lemma lem3573156 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term472 _91307 _91560 t s f) = (term489 _91307 _91560 t s f).
Proof. exact (EQ_MP (@lem3573155 _91307 _91560 t s f) (@lem3573136 _91307 _91560 t s f)). Qed.
Lemma lem3573158 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3573159 {_91307 _91560 : Type'} (P : Prop) (Q : type198 _91307 _91560) : (term490 _91307 _91560 P Q) = (term491 _91307 _91560 P Q).
Proof. exact (@lem3573158 (type803 _91307 _91560) P Q). Qed.
Lemma lem3573160 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term492 _91307 _91560 x t s f) = (term493 _91307 _91560 x t s f).
Proof. exact (@lem3573159 _91307 _91560 (term316 _91307 _91560 t s f x) (term470 _91307 _91560 t s f)). Qed.
Lemma lem3573161 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) : (term494 _91307 _91560 t s f y) = (term468 _91307 _91560 t s f y).
Proof. exact (eq_refl (term494 _91307 _91560 t s f y)). Qed.
Lemma lem3573162 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term495 _91307 _91560 t s f) = (term470 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : type803 _91307 _91560 => @lem3573161 _91307 _91560 t s f y)). Qed.
Lemma lem3573163 {_91307 _91560 : Type'} : (@ex ((_91560 -> _91307) -> _91560)) = (@ex ((_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573164 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term496 _91307 _91560 t s f) = (term471 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573163 _91307 _91560) (@lem3573162 _91307 _91560 t s f)). Qed.
Lemma lem3573165 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) : (term484 _91307 _91560 t s f x) = (term484 _91307 _91560 t s f x).
Proof. exact (eq_refl (term484 _91307 _91560 t s f x)). Qed.
Lemma lem3573166 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term492 _91307 _91560 x t s f) = (term486 _91307 _91560 x t s f).
Proof. exact (MK_COMB (@lem3573165 _91307 _91560 t s f x) (@lem3573164 _91307 _91560 t s f)). Qed.
Lemma lem3573167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573168 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term497 _91307 _91560 x t s f) = (term498 _91307 _91560 x t s f).
Proof. exact (MK_COMB (@lem3573167) (@lem3573166 _91307 _91560 x t s f)). Qed.
Lemma lem3573169 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) : (term494 _91307 _91560 t s f y) = (term468 _91307 _91560 t s f y).
Proof. exact (eq_refl (term494 _91307 _91560 t s f y)). Qed.
Lemma lem3573170 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) : (term484 _91307 _91560 t s f x) = (term484 _91307 _91560 t s f x).
Proof. exact (eq_refl (term484 _91307 _91560 t s f x)). Qed.
Lemma lem3573171 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) : (term499 _91307 _91560 x t s f y) = (term500 _91307 _91560 x t s f y).
Proof. exact (MK_COMB (@lem3573170 _91307 _91560 t s f x) (@lem3573169 _91307 _91560 t s f y)). Qed.
Lemma lem3573172 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term501 _91307 _91560 x t s f) = (term502 _91307 _91560 x t s f).
Proof. exact (fun_ext (fun y : type803 _91307 _91560 => @lem3573171 _91307 _91560 x t s f y)). Qed.
Lemma lem3573173 {_91307 _91560 : Type'} : (@ex ((_91560 -> _91307) -> _91560)) = (@ex ((_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573174 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term493 _91307 _91560 x t s f) = (term503 _91307 _91560 x t s f).
Proof. exact (MK_COMB (@lem3573173 _91307 _91560) (@lem3573172 _91307 _91560 x t s f)). Qed.
Lemma lem3573175 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term492 _91307 _91560 x t s f) = (term493 _91307 _91560 x t s f)) = ((term486 _91307 _91560 x t s f) = (term503 _91307 _91560 x t s f)).
Proof. exact (MK_COMB (@lem3573168 _91307 _91560 x t s f) (@lem3573174 _91307 _91560 x t s f)). Qed.
Lemma lem3573176 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term486 _91307 _91560 x t s f) = (term503 _91307 _91560 x t s f).
Proof. exact (EQ_MP (@lem3573175 _91307 _91560 x t s f) (@lem3573160 _91307 _91560 x t s f)). Qed.
Lemma lem3573177 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term488 _91307 _91560 t s f) = (term504 _91307 _91560 t s f).
Proof. exact (fun_ext (fun x : _91560 -> _91307 => @lem3573176 _91307 _91560 x t s f)). Qed.
Lemma lem3573178 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3573179 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term489 _91307 _91560 t s f) = (term505 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573178 _91307 _91560) (@lem3573177 _91307 _91560 t s f)). Qed.
Lemma lem3573180 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term472 _91307 _91560 t s f) = (term505 _91307 _91560 t s f).
Proof. exact (TRANS (@lem3573156 _91307 _91560 t s f) (@lem3573179 _91307 _91560 t s f)). Qed.
Lemma lem3573181 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term335 _91307 _91560 t s f) = (term505 _91307 _91560 t s f).
Proof. exact (TRANS (@lem3573130 _91307 _91560 t s f) (@lem3573180 _91307 _91560 t s f)). Qed.
Lemma lem3573182 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term352 _91307 _91560 s f) = (term506 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573181 _91307 _91560 t s f)). Qed.
Lemma lem3573183 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573184 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term363 _91307 _91560 s f) = (term507 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573183 _91560) (@lem3573182 _91307 _91560 s f)). Qed.
Lemma lem3573186 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573187 {_91307 _91560 : Type'} (P : type856 _91307 _91560) : (term508 _91307 _91560 P) = (term509 _91307 _91560 P).
Proof. exact (@lem3573186 (_91560 -> Prop) (_91560 -> _91307) P). Qed.
Lemma lem3573188 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term510 _91307 _91560 s f) = (term511 _91307 _91560 s f).
Proof. exact (@lem3573187 _91307 _91560 (term512 _91307 _91560 s f)). Qed.
Lemma lem3573189 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term513 _91307 _91560 s f t) = (term504 _91307 _91560 t s f).
Proof. exact (eq_refl (term513 _91307 _91560 s f t)). Qed.
Lemma lem3573190 {_91307 _91560 : Type'} (x : _91560 -> _91307) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3573191 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (x : _91560 -> _91307) : (term514 _91307 _91560 s f t x) = (term515 _91307 _91560 t s f x).
Proof. exact (MK_COMB (@lem3573189 _91307 _91560 t s f) (@lem3573190 _91307 _91560 x)). Qed.
Lemma lem3573192 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term515 _91307 _91560 t s f x) = (term503 _91307 _91560 x t s f).
Proof. exact (eq_refl (term515 _91307 _91560 t s f x)). Qed.
Lemma lem3573193 {_91307 _91560 : Type'} (x : _91560 -> _91307) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term514 _91307 _91560 s f t x) = (term503 _91307 _91560 x t s f).
Proof. exact (TRANS (@lem3573191 _91307 _91560 t s f x) (@lem3573192 _91307 _91560 x t s f)). Qed.
Lemma lem3573194 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term516 _91307 _91560 s f t) = (term504 _91307 _91560 t s f).
Proof. exact (fun_ext (fun x : _91560 -> _91307 => @lem3573193 _91307 _91560 x t s f)). Qed.
Lemma lem3573195 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3573196 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term517 _91307 _91560 s f t) = (term505 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573195 _91307 _91560) (@lem3573194 _91307 _91560 t s f)). Qed.
Lemma lem3573197 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term518 _91307 _91560 s f) = (term506 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573196 _91307 _91560 t s f)). Qed.
Lemma lem3573198 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573199 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term510 _91307 _91560 s f) = (term507 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573198 _91560) (@lem3573197 _91307 _91560 s f)). Qed.
Lemma lem3573200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573201 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term519 _91307 _91560 s f) = (term520 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573200) (@lem3573199 _91307 _91560 s f)). Qed.
Lemma lem3573202 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term513 _91307 _91560 s f t) = (term504 _91307 _91560 t s f).
Proof. exact (eq_refl (term513 _91307 _91560 s f t)). Qed.
Lemma lem3573203 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem3573204 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : type861 _91307 _91560) (t : _91560 -> Prop) : (term521 _91307 _91560 s f x t) = (term522 _91307 _91560 s f x t).
Proof. exact (MK_COMB (@lem3573202 _91307 _91560 t s f) (@lem3573203 _91307 _91560 x t)). Qed.
Lemma lem3573205 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term522 _91307 _91560 s f x t) = (term523 _91307 _91560 x t s f).
Proof. exact (eq_refl (term522 _91307 _91560 s f x t)). Qed.
Lemma lem3573206 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term521 _91307 _91560 s f x t) = (term523 _91307 _91560 x t s f).
Proof. exact (TRANS (@lem3573204 _91307 _91560 s f x t) (@lem3573205 _91307 _91560 x t s f)). Qed.
Lemma lem3573207 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term524 _91307 _91560 s f x) = (term525 _91307 _91560 x s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573206 _91307 _91560 x t s f)). Qed.
Lemma lem3573208 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573209 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term526 _91307 _91560 s f x) = (term527 _91307 _91560 x s f).
Proof. exact (MK_COMB (@lem3573208 _91560) (@lem3573207 _91307 _91560 x s f)). Qed.
Lemma lem3573210 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term528 _91307 _91560 s f) = (term529 _91307 _91560 s f).
Proof. exact (fun_ext (fun x : type861 _91307 _91560 => @lem3573209 _91307 _91560 x s f)). Qed.
Lemma lem3573211 {_91307 _91560 : Type'} : (@ex ((_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573212 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term511 _91307 _91560 s f) = (term530 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573211 _91307 _91560) (@lem3573210 _91307 _91560 s f)). Qed.
Lemma lem3573213 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term510 _91307 _91560 s f) = (term511 _91307 _91560 s f)) = ((term507 _91307 _91560 s f) = (term530 _91307 _91560 s f)).
Proof. exact (MK_COMB (@lem3573201 _91307 _91560 s f) (@lem3573212 _91307 _91560 s f)). Qed.
Lemma lem3573214 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term507 _91307 _91560 s f) = (term530 _91307 _91560 s f).
Proof. exact (EQ_MP (@lem3573213 _91307 _91560 s f) (@lem3573188 _91307 _91560 s f)). Qed.
Lemma lem3573216 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573217 {_91307 _91560 : Type'} (P : type828 _91307 _91560) : (term531 _91307 _91560 P) = (term532 _91307 _91560 P).
Proof. exact (@lem3573216 (_91560 -> Prop) (type803 _91307 _91560) P). Qed.
Lemma lem3573218 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term533 _91307 _91560 x s f) = (term534 _91307 _91560 x s f).
Proof. exact (@lem3573217 _91307 _91560 (term535 _91307 _91560 x s f)). Qed.
Lemma lem3573219 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term536 _91307 _91560 x s f t) = (term537 _91307 _91560 x t s f).
Proof. exact (eq_refl (term536 _91307 _91560 x s f t)). Qed.
Lemma lem3573220 {_91307 _91560 : Type'} (y : type803 _91307 _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3573221 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) : (term538 _91307 _91560 x s f t y) = (term539 _91307 _91560 x t s f y).
Proof. exact (MK_COMB (@lem3573219 _91307 _91560 x t s f) (@lem3573220 _91307 _91560 y)). Qed.
Lemma lem3573222 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) : (term539 _91307 _91560 x t s f y) = (term540 _91307 _91560 x t s f y).
Proof. exact (eq_refl (term539 _91307 _91560 x t s f y)). Qed.
Lemma lem3573223 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type803 _91307 _91560) : (term538 _91307 _91560 x s f t y) = (term540 _91307 _91560 x t s f y).
Proof. exact (TRANS (@lem3573221 _91307 _91560 x t s f y) (@lem3573222 _91307 _91560 x t s f y)). Qed.
Lemma lem3573224 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term541 _91307 _91560 x s f t) = (term537 _91307 _91560 x t s f).
Proof. exact (fun_ext (fun y : type803 _91307 _91560 => @lem3573223 _91307 _91560 x t s f y)). Qed.
Lemma lem3573225 {_91307 _91560 : Type'} : (@ex ((_91560 -> _91307) -> _91560)) = (@ex ((_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573226 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term542 _91307 _91560 x s f t) = (term523 _91307 _91560 x t s f).
Proof. exact (MK_COMB (@lem3573225 _91307 _91560) (@lem3573224 _91307 _91560 x t s f)). Qed.
Lemma lem3573227 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term543 _91307 _91560 x s f) = (term525 _91307 _91560 x s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573226 _91307 _91560 x t s f)). Qed.
Lemma lem3573228 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573229 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term533 _91307 _91560 x s f) = (term527 _91307 _91560 x s f).
Proof. exact (MK_COMB (@lem3573228 _91560) (@lem3573227 _91307 _91560 x s f)). Qed.
Lemma lem3573230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573231 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term544 _91307 _91560 x s f) = (term545 _91307 _91560 x s f).
Proof. exact (MK_COMB (@lem3573230) (@lem3573229 _91307 _91560 x s f)). Qed.
Lemma lem3573232 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term536 _91307 _91560 x s f t) = (term537 _91307 _91560 x t s f).
Proof. exact (eq_refl (term536 _91307 _91560 x s f t)). Qed.
Lemma lem3573233 {_91307 _91560 : Type'} (y : type855 _91307 _91560) (t : _91560 -> Prop) : (y t) = (y t).
Proof. exact (eq_refl (y t)). Qed.
Lemma lem3573234 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type855 _91307 _91560) (t : _91560 -> Prop) : (term546 _91307 _91560 x s f y t) = (term547 _91307 _91560 x s f y t).
Proof. exact (MK_COMB (@lem3573232 _91307 _91560 x t s f) (@lem3573233 _91307 _91560 y t)). Qed.
Lemma lem3573235 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type855 _91307 _91560) (t : _91560 -> Prop) : (term547 _91307 _91560 x s f y t) = (term548 _91307 _91560 x s f y t).
Proof. exact (eq_refl (term547 _91307 _91560 x s f y t)). Qed.
Lemma lem3573236 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type855 _91307 _91560) (t : _91560 -> Prop) : (term546 _91307 _91560 x s f y t) = (term548 _91307 _91560 x s f y t).
Proof. exact (TRANS (@lem3573234 _91307 _91560 x s f y t) (@lem3573235 _91307 _91560 x s f y t)). Qed.
Lemma lem3573237 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type855 _91307 _91560) : (term549 _91307 _91560 x s f y) = (term550 _91307 _91560 x s f y).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573236 _91307 _91560 x s f y t)). Qed.
Lemma lem3573238 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573239 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type855 _91307 _91560) : (term551 _91307 _91560 x s f y) = (term552 _91307 _91560 x s f y).
Proof. exact (MK_COMB (@lem3573238 _91560) (@lem3573237 _91307 _91560 x s f y)). Qed.
Lemma lem3573240 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term553 _91307 _91560 x s f) = (term554 _91307 _91560 x s f).
Proof. exact (fun_ext (fun y : type855 _91307 _91560 => @lem3573239 _91307 _91560 x s f y)). Qed.
Lemma lem3573241 {_91307 _91560 : Type'} : (@ex ((_91560 -> Prop) -> (_91560 -> _91307) -> _91560)) = (@ex ((_91560 -> Prop) -> (_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> (_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573242 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term534 _91307 _91560 x s f) = (term555 _91307 _91560 x s f).
Proof. exact (MK_COMB (@lem3573241 _91307 _91560) (@lem3573240 _91307 _91560 x s f)). Qed.
Lemma lem3573243 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term533 _91307 _91560 x s f) = (term534 _91307 _91560 x s f)) = ((term527 _91307 _91560 x s f) = (term555 _91307 _91560 x s f)).
Proof. exact (MK_COMB (@lem3573231 _91307 _91560 x s f) (@lem3573242 _91307 _91560 x s f)). Qed.
Lemma lem3573244 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term527 _91307 _91560 x s f) = (term555 _91307 _91560 x s f).
Proof. exact (EQ_MP (@lem3573243 _91307 _91560 x s f) (@lem3573218 _91307 _91560 x s f)). Qed.
Lemma lem3573245 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term529 _91307 _91560 s f) = (term556 _91307 _91560 s f).
Proof. exact (fun_ext (fun x : type861 _91307 _91560 => @lem3573244 _91307 _91560 x s f)). Qed.
Lemma lem3573246 {_91307 _91560 : Type'} : (@ex ((_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573247 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term530 _91307 _91560 s f) = (term557 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573246 _91307 _91560) (@lem3573245 _91307 _91560 s f)). Qed.
Lemma lem3573248 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term507 _91307 _91560 s f) = (term557 _91307 _91560 s f).
Proof. exact (TRANS (@lem3573214 _91307 _91560 s f) (@lem3573247 _91307 _91560 s f)). Qed.
Lemma lem3573249 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term363 _91307 _91560 s f) = (term557 _91307 _91560 s f).
Proof. exact (TRANS (@lem3573184 _91307 _91560 s f) (@lem3573248 _91307 _91560 s f)). Qed.
Lemma lem3573250 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term376 _91307 _91560 s) = (term558 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573249 _91307 _91560 s f)). Qed.
Lemma lem3573251 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573252 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term387 _91307 _91560 s) = (term559 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573251 _91307 _91560) (@lem3573250 _91307 _91560 s)). Qed.
Lemma lem3573254 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573255 {_91307 _91560 : Type'} (P : type507 _91307 _91560) : (term560 _91307 _91560 P) = (term561 _91307 _91560 P).
Proof. exact (@lem3573254 (_91307 -> _91560) (type861 _91307 _91560) P). Qed.
Lemma lem3573256 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term562 _91307 _91560 s) = (term563 _91307 _91560 s).
Proof. exact (@lem3573255 _91307 _91560 (term564 _91307 _91560 s)). Qed.
Lemma lem3573257 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term565 _91307 _91560 s f) = (term556 _91307 _91560 s f).
Proof. exact (eq_refl (term565 _91307 _91560 s f)). Qed.
Lemma lem3573258 {_91307 _91560 : Type'} (x : type861 _91307 _91560) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3573259 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (x : type861 _91307 _91560) : (term566 _91307 _91560 s f x) = (term567 _91307 _91560 s f x).
Proof. exact (MK_COMB (@lem3573257 _91307 _91560 s f) (@lem3573258 _91307 _91560 x)). Qed.
Lemma lem3573260 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term567 _91307 _91560 s f x) = (term555 _91307 _91560 x s f).
Proof. exact (eq_refl (term567 _91307 _91560 s f x)). Qed.
Lemma lem3573261 {_91307 _91560 : Type'} (x : type861 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term566 _91307 _91560 s f x) = (term555 _91307 _91560 x s f).
Proof. exact (TRANS (@lem3573259 _91307 _91560 s f x) (@lem3573260 _91307 _91560 x s f)). Qed.
Lemma lem3573262 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term568 _91307 _91560 s f) = (term556 _91307 _91560 s f).
Proof. exact (fun_ext (fun x : type861 _91307 _91560 => @lem3573261 _91307 _91560 x s f)). Qed.
Lemma lem3573263 {_91307 _91560 : Type'} : (@ex ((_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573264 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term569 _91307 _91560 s f) = (term557 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573263 _91307 _91560) (@lem3573262 _91307 _91560 s f)). Qed.
Lemma lem3573265 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term570 _91307 _91560 s) = (term558 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573264 _91307 _91560 s f)). Qed.
Lemma lem3573266 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573267 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term562 _91307 _91560 s) = (term559 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573266 _91307 _91560) (@lem3573265 _91307 _91560 s)). Qed.
Lemma lem3573268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573269 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term571 _91307 _91560 s) = (term572 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573268) (@lem3573267 _91307 _91560 s)). Qed.
Lemma lem3573270 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term565 _91307 _91560 s f) = (term556 _91307 _91560 s f).
Proof. exact (eq_refl (term565 _91307 _91560 s f)). Qed.
Lemma lem3573271 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (f : _91307 -> _91560) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3573272 {_91307 _91560 : Type'} (s : _91307 -> Prop) (x : type532 _91307 _91560) (f : _91307 -> _91560) : (term573 _91307 _91560 s x f) = (term574 _91307 _91560 s x f).
Proof. exact (MK_COMB (@lem3573270 _91307 _91560 s f) (@lem3573271 _91307 _91560 x f)). Qed.
Lemma lem3573273 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term574 _91307 _91560 s x f) = (term575 _91307 _91560 x s f).
Proof. exact (eq_refl (term574 _91307 _91560 s x f)). Qed.
Lemma lem3573274 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term573 _91307 _91560 s x f) = (term575 _91307 _91560 x s f).
Proof. exact (TRANS (@lem3573272 _91307 _91560 s x f) (@lem3573273 _91307 _91560 x s f)). Qed.
Lemma lem3573275 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term576 _91307 _91560 s x) = (term577 _91307 _91560 x s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573274 _91307 _91560 x s f)). Qed.
Lemma lem3573276 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573277 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term578 _91307 _91560 s x) = (term579 _91307 _91560 x s).
Proof. exact (MK_COMB (@lem3573276 _91307 _91560) (@lem3573275 _91307 _91560 x s)). Qed.
Lemma lem3573278 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term580 _91307 _91560 s) = (term581 _91307 _91560 s).
Proof. exact (fun_ext (fun x : type532 _91307 _91560 => @lem3573277 _91307 _91560 x s)). Qed.
Lemma lem3573279 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573280 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term563 _91307 _91560 s) = (term582 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573279 _91307 _91560) (@lem3573278 _91307 _91560 s)). Qed.
Lemma lem3573281 {_91307 _91560 : Type'} (s : _91307 -> Prop) : ((term562 _91307 _91560 s) = (term563 _91307 _91560 s)) = ((term559 _91307 _91560 s) = (term582 _91307 _91560 s)).
Proof. exact (MK_COMB (@lem3573269 _91307 _91560 s) (@lem3573280 _91307 _91560 s)). Qed.
Lemma lem3573282 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term559 _91307 _91560 s) = (term582 _91307 _91560 s).
Proof. exact (EQ_MP (@lem3573281 _91307 _91560 s) (@lem3573256 _91307 _91560 s)). Qed.
Lemma lem3573284 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573285 {_91307 _91560 : Type'} (P : type506 _91307 _91560) : (term583 _91307 _91560 P) = (term584 _91307 _91560 P).
Proof. exact (@lem3573284 (_91307 -> _91560) (type855 _91307 _91560) P). Qed.
Lemma lem3573286 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term585 _91307 _91560 x s) = (term586 _91307 _91560 x s).
Proof. exact (@lem3573285 _91307 _91560 (term587 _91307 _91560 x s)). Qed.
Lemma lem3573287 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term588 _91307 _91560 x s f) = (term589 _91307 _91560 x s f).
Proof. exact (eq_refl (term588 _91307 _91560 x s f)). Qed.
Lemma lem3573288 {_91307 _91560 : Type'} (y : type855 _91307 _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3573289 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type855 _91307 _91560) : (term590 _91307 _91560 x s f y) = (term591 _91307 _91560 x s f y).
Proof. exact (MK_COMB (@lem3573287 _91307 _91560 x s f) (@lem3573288 _91307 _91560 y)). Qed.
Lemma lem3573290 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type855 _91307 _91560) : (term591 _91307 _91560 x s f y) = (term592 _91307 _91560 x s f y).
Proof. exact (eq_refl (term591 _91307 _91560 x s f y)). Qed.
Lemma lem3573291 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type855 _91307 _91560) : (term590 _91307 _91560 x s f y) = (term592 _91307 _91560 x s f y).
Proof. exact (TRANS (@lem3573289 _91307 _91560 x s f y) (@lem3573290 _91307 _91560 x s f y)). Qed.
Lemma lem3573292 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term593 _91307 _91560 x s f) = (term589 _91307 _91560 x s f).
Proof. exact (fun_ext (fun y : type855 _91307 _91560 => @lem3573291 _91307 _91560 x s f y)). Qed.
Lemma lem3573293 {_91307 _91560 : Type'} : (@ex ((_91560 -> Prop) -> (_91560 -> _91307) -> _91560)) = (@ex ((_91560 -> Prop) -> (_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> (_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573294 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term594 _91307 _91560 x s f) = (term575 _91307 _91560 x s f).
Proof. exact (MK_COMB (@lem3573293 _91307 _91560) (@lem3573292 _91307 _91560 x s f)). Qed.
Lemma lem3573295 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term595 _91307 _91560 x s) = (term577 _91307 _91560 x s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573294 _91307 _91560 x s f)). Qed.
Lemma lem3573296 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573297 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term585 _91307 _91560 x s) = (term579 _91307 _91560 x s).
Proof. exact (MK_COMB (@lem3573296 _91307 _91560) (@lem3573295 _91307 _91560 x s)). Qed.
Lemma lem3573298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573299 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term596 _91307 _91560 x s) = (term597 _91307 _91560 x s).
Proof. exact (MK_COMB (@lem3573298) (@lem3573297 _91307 _91560 x s)). Qed.
Lemma lem3573300 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term588 _91307 _91560 x s f) = (term589 _91307 _91560 x s f).
Proof. exact (eq_refl (term588 _91307 _91560 x s f)). Qed.
Lemma lem3573301 {_91307 _91560 : Type'} (y : type531 _91307 _91560) (f : _91307 -> _91560) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3573302 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (y : type531 _91307 _91560) (f : _91307 -> _91560) : (term598 _91307 _91560 x s y f) = (term599 _91307 _91560 x s y f).
Proof. exact (MK_COMB (@lem3573300 _91307 _91560 x s f) (@lem3573301 _91307 _91560 y f)). Qed.
Lemma lem3573303 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (y : type531 _91307 _91560) (f : _91307 -> _91560) : (term599 _91307 _91560 x s y f) = (term600 _91307 _91560 x s y f).
Proof. exact (eq_refl (term599 _91307 _91560 x s y f)). Qed.
Lemma lem3573304 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (y : type531 _91307 _91560) (f : _91307 -> _91560) : (term598 _91307 _91560 x s y f) = (term600 _91307 _91560 x s y f).
Proof. exact (TRANS (@lem3573302 _91307 _91560 x s y f) (@lem3573303 _91307 _91560 x s y f)). Qed.
Lemma lem3573305 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (y : type531 _91307 _91560) : (term601 _91307 _91560 x s y) = (term602 _91307 _91560 x s y).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573304 _91307 _91560 x s y f)). Qed.
Lemma lem3573306 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573307 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) (y : type531 _91307 _91560) : (term603 _91307 _91560 x s y) = (term604 _91307 _91560 x s y).
Proof. exact (MK_COMB (@lem3573306 _91307 _91560) (@lem3573305 _91307 _91560 x s y)). Qed.
Lemma lem3573308 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term605 _91307 _91560 x s) = (term606 _91307 _91560 x s).
Proof. exact (fun_ext (fun y : type531 _91307 _91560 => @lem3573307 _91307 _91560 x s y)). Qed.
Lemma lem3573309 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573310 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term586 _91307 _91560 x s) = (term607 _91307 _91560 x s).
Proof. exact (MK_COMB (@lem3573309 _91307 _91560) (@lem3573308 _91307 _91560 x s)). Qed.
Lemma lem3573311 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : ((term585 _91307 _91560 x s) = (term586 _91307 _91560 x s)) = ((term579 _91307 _91560 x s) = (term607 _91307 _91560 x s)).
Proof. exact (MK_COMB (@lem3573299 _91307 _91560 x s) (@lem3573310 _91307 _91560 x s)). Qed.
Lemma lem3573312 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term579 _91307 _91560 x s) = (term607 _91307 _91560 x s).
Proof. exact (EQ_MP (@lem3573311 _91307 _91560 x s) (@lem3573286 _91307 _91560 x s)). Qed.
Lemma lem3573313 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term581 _91307 _91560 s) = (term608 _91307 _91560 s).
Proof. exact (fun_ext (fun x : type532 _91307 _91560 => @lem3573312 _91307 _91560 x s)). Qed.
Lemma lem3573314 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573315 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term582 _91307 _91560 s) = (term609 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573314 _91307 _91560) (@lem3573313 _91307 _91560 s)). Qed.
Lemma lem3573316 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term559 _91307 _91560 s) = (term609 _91307 _91560 s).
Proof. exact (TRANS (@lem3573282 _91307 _91560 s) (@lem3573315 _91307 _91560 s)). Qed.
Lemma lem3573317 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term387 _91307 _91560 s) = (term609 _91307 _91560 s).
Proof. exact (TRANS (@lem3573252 _91307 _91560 s) (@lem3573316 _91307 _91560 s)). Qed.
Lemma lem3573318 {_91307 _91560 : Type'} : (term398 _91307 _91560) = (term610 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573317 _91307 _91560 s)). Qed.
Lemma lem3573319 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573320 {_91307 _91560 : Type'} : (term409 _91307 _91560) = (term611 _91307 _91560).
Proof. exact (MK_COMB (@lem3573319 _91307) (@lem3573318 _91307 _91560)). Qed.
Lemma lem3573322 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573323 {_91307 _91560 : Type'} (P : type591 _91307 _91560) : (term612 _91307 _91560 P) = (term613 _91307 _91560 P).
Proof. exact (@lem3573322 (_91307 -> Prop) (type532 _91307 _91560) P). Qed.
Lemma lem3573324 {_91307 _91560 : Type'} : (term614 _91307 _91560) = (term615 _91307 _91560).
Proof. exact (@lem3573323 _91307 _91560 (term616 _91307 _91560)). Qed.
Lemma lem3573325 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term617 _91307 _91560 s) = (term608 _91307 _91560 s).
Proof. exact (eq_refl (term617 _91307 _91560 s)). Qed.
Lemma lem3573326 {_91307 _91560 : Type'} (x : type532 _91307 _91560) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3573327 {_91307 _91560 : Type'} (s : _91307 -> Prop) (x : type532 _91307 _91560) : (term618 _91307 _91560 s x) = (term619 _91307 _91560 s x).
Proof. exact (MK_COMB (@lem3573325 _91307 _91560 s) (@lem3573326 _91307 _91560 x)). Qed.
Lemma lem3573328 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term619 _91307 _91560 s x) = (term607 _91307 _91560 x s).
Proof. exact (eq_refl (term619 _91307 _91560 s x)). Qed.
Lemma lem3573329 {_91307 _91560 : Type'} (x : type532 _91307 _91560) (s : _91307 -> Prop) : (term618 _91307 _91560 s x) = (term607 _91307 _91560 x s).
Proof. exact (TRANS (@lem3573327 _91307 _91560 s x) (@lem3573328 _91307 _91560 x s)). Qed.
Lemma lem3573330 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term620 _91307 _91560 s) = (term608 _91307 _91560 s).
Proof. exact (fun_ext (fun x : type532 _91307 _91560 => @lem3573329 _91307 _91560 x s)). Qed.
Lemma lem3573331 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573332 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term621 _91307 _91560 s) = (term609 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573331 _91307 _91560) (@lem3573330 _91307 _91560 s)). Qed.
Lemma lem3573333 {_91307 _91560 : Type'} : (term622 _91307 _91560) = (term610 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573332 _91307 _91560 s)). Qed.
Lemma lem3573334 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573335 {_91307 _91560 : Type'} : (term614 _91307 _91560) = (term611 _91307 _91560).
Proof. exact (MK_COMB (@lem3573334 _91307) (@lem3573333 _91307 _91560)). Qed.
Lemma lem3573336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573337 {_91307 _91560 : Type'} : (term623 _91307 _91560) = (term624 _91307 _91560).
Proof. exact (MK_COMB (@lem3573336) (@lem3573335 _91307 _91560)). Qed.
Lemma lem3573338 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term617 _91307 _91560 s) = (term608 _91307 _91560 s).
Proof. exact (eq_refl (term617 _91307 _91560 s)). Qed.
Lemma lem3573339 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3573340 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) : (term625 _91307 _91560 x s) = (term626 _91307 _91560 x s).
Proof. exact (MK_COMB (@lem3573338 _91307 _91560 s) (@lem3573339 _91307 _91560 x s)). Qed.
Lemma lem3573341 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) : (term626 _91307 _91560 x s) = (term627 _91307 _91560 x s).
Proof. exact (eq_refl (term626 _91307 _91560 x s)). Qed.
Lemma lem3573342 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) : (term625 _91307 _91560 x s) = (term627 _91307 _91560 x s).
Proof. exact (TRANS (@lem3573340 _91307 _91560 x s) (@lem3573341 _91307 _91560 x s)). Qed.
Lemma lem3573343 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term628 _91307 _91560 x) = (term629 _91307 _91560 x).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573342 _91307 _91560 x s)). Qed.
Lemma lem3573344 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573345 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term630 _91307 _91560 x) = (term631 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573344 _91307) (@lem3573343 _91307 _91560 x)). Qed.
Lemma lem3573346 {_91307 _91560 : Type'} : (term632 _91307 _91560) = (term633 _91307 _91560).
Proof. exact (fun_ext (fun x : type629 _91307 _91560 => @lem3573345 _91307 _91560 x)). Qed.
Lemma lem3573347 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573348 {_91307 _91560 : Type'} : (term615 _91307 _91560) = (term634 _91307 _91560).
Proof. exact (MK_COMB (@lem3573347 _91307 _91560) (@lem3573346 _91307 _91560)). Qed.
Lemma lem3573349 {_91307 _91560 : Type'} : ((term614 _91307 _91560) = (term615 _91307 _91560)) = ((term611 _91307 _91560) = (term634 _91307 _91560)).
Proof. exact (MK_COMB (@lem3573337 _91307 _91560) (@lem3573348 _91307 _91560)). Qed.
Lemma lem3573350 {_91307 _91560 : Type'} : (term611 _91307 _91560) = (term634 _91307 _91560).
Proof. exact (EQ_MP (@lem3573349 _91307 _91560) (@lem3573324 _91307 _91560)). Qed.
Lemma lem3573352 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573353 {_91307 _91560 : Type'} (P : type590 _91307 _91560) : (term635 _91307 _91560 P) = (term636 _91307 _91560 P).
Proof. exact (@lem3573352 (_91307 -> Prop) (type531 _91307 _91560) P). Qed.
Lemma lem3573354 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term637 _91307 _91560 x) = (term638 _91307 _91560 x).
Proof. exact (@lem3573353 _91307 _91560 (term639 _91307 _91560 x)). Qed.
Lemma lem3573355 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) : (term640 _91307 _91560 x s) = (term641 _91307 _91560 x s).
Proof. exact (eq_refl (term640 _91307 _91560 x s)). Qed.
Lemma lem3573356 {_91307 _91560 : Type'} (y : type531 _91307 _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3573357 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) (y : type531 _91307 _91560) : (term642 _91307 _91560 x s y) = (term643 _91307 _91560 x s y).
Proof. exact (MK_COMB (@lem3573355 _91307 _91560 x s) (@lem3573356 _91307 _91560 y)). Qed.
Lemma lem3573358 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) (y : type531 _91307 _91560) : (term643 _91307 _91560 x s y) = (term644 _91307 _91560 x s y).
Proof. exact (eq_refl (term643 _91307 _91560 x s y)). Qed.
Lemma lem3573359 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) (y : type531 _91307 _91560) : (term642 _91307 _91560 x s y) = (term644 _91307 _91560 x s y).
Proof. exact (TRANS (@lem3573357 _91307 _91560 x s y) (@lem3573358 _91307 _91560 x s y)). Qed.
Lemma lem3573360 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) : (term645 _91307 _91560 x s) = (term641 _91307 _91560 x s).
Proof. exact (fun_ext (fun y : type531 _91307 _91560 => @lem3573359 _91307 _91560 x s y)). Qed.
Lemma lem3573361 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573362 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) : (term646 _91307 _91560 x s) = (term627 _91307 _91560 x s).
Proof. exact (MK_COMB (@lem3573361 _91307 _91560) (@lem3573360 _91307 _91560 x s)). Qed.
Lemma lem3573363 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term647 _91307 _91560 x) = (term629 _91307 _91560 x).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573362 _91307 _91560 x s)). Qed.
Lemma lem3573364 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573365 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term637 _91307 _91560 x) = (term631 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573364 _91307) (@lem3573363 _91307 _91560 x)). Qed.
Lemma lem3573366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573367 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term648 _91307 _91560 x) = (term649 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573366) (@lem3573365 _91307 _91560 x)). Qed.
Lemma lem3573368 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (s : _91307 -> Prop) : (term640 _91307 _91560 x s) = (term641 _91307 _91560 x s).
Proof. exact (eq_refl (term640 _91307 _91560 x s)). Qed.
Lemma lem3573369 {_91307 _91560 : Type'} (y : type628 _91307 _91560) (s : _91307 -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3573370 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (s : _91307 -> Prop) : (term650 _91307 _91560 x y s) = (term651 _91307 _91560 x y s).
Proof. exact (MK_COMB (@lem3573368 _91307 _91560 x s) (@lem3573369 _91307 _91560 y s)). Qed.
Lemma lem3573371 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (s : _91307 -> Prop) : (term651 _91307 _91560 x y s) = (term652 _91307 _91560 x y s).
Proof. exact (eq_refl (term651 _91307 _91560 x y s)). Qed.
Lemma lem3573372 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (s : _91307 -> Prop) : (term650 _91307 _91560 x y s) = (term652 _91307 _91560 x y s).
Proof. exact (TRANS (@lem3573370 _91307 _91560 x y s) (@lem3573371 _91307 _91560 x y s)). Qed.
Lemma lem3573373 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term653 _91307 _91560 x y) = (term654 _91307 _91560 x y).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573372 _91307 _91560 x y s)). Qed.
Lemma lem3573374 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573375 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term655 _91307 _91560 x y) = (term656 _91307 _91560 x y).
Proof. exact (MK_COMB (@lem3573374 _91307) (@lem3573373 _91307 _91560 x y)). Qed.
Lemma lem3573376 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term657 _91307 _91560 x) = (term658 _91307 _91560 x).
Proof. exact (fun_ext (fun y : type628 _91307 _91560 => @lem3573375 _91307 _91560 x y)). Qed.
Lemma lem3573377 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573378 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term638 _91307 _91560 x) = (term659 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573377 _91307 _91560) (@lem3573376 _91307 _91560 x)). Qed.
Lemma lem3573379 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : ((term637 _91307 _91560 x) = (term638 _91307 _91560 x)) = ((term631 _91307 _91560 x) = (term659 _91307 _91560 x)).
Proof. exact (MK_COMB (@lem3573367 _91307 _91560 x) (@lem3573378 _91307 _91560 x)). Qed.
Lemma lem3573380 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term631 _91307 _91560 x) = (term659 _91307 _91560 x).
Proof. exact (EQ_MP (@lem3573379 _91307 _91560 x) (@lem3573354 _91307 _91560 x)). Qed.
Lemma lem3573381 {_91307 _91560 : Type'} : (term633 _91307 _91560) = (term660 _91307 _91560).
Proof. exact (fun_ext (fun x : type629 _91307 _91560 => @lem3573380 _91307 _91560 x)). Qed.
Lemma lem3573382 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573383 {_91307 _91560 : Type'} : (term634 _91307 _91560) = (term661 _91307 _91560).
Proof. exact (MK_COMB (@lem3573382 _91307 _91560) (@lem3573381 _91307 _91560)). Qed.
Lemma lem3573384 {_91307 _91560 : Type'} : (term611 _91307 _91560) = (term661 _91307 _91560).
Proof. exact (TRANS (@lem3573350 _91307 _91560) (@lem3573383 _91307 _91560)). Qed.
Lemma lem3573385 {_91307 _91560 : Type'} : (term409 _91307 _91560) = (term661 _91307 _91560).
Proof. exact (TRANS (@lem3573320 _91307 _91560) (@lem3573384 _91307 _91560)). Qed.
Lemma lem3573386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3573387 {_91307 _91560 : Type'} : (term411 _91307 _91560) = (term662 _91307 _91560).
Proof. exact (MK_COMB (@lem3573386) (@lem3573385 _91307 _91560)). Qed.
Lemma lem3573391 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3573392 {_91560 : Type'} (P : _91560 -> Prop) (Q : Prop) : (term205 _91560 P Q) = (term206 _91560 P Q).
Proof. exact (@lem3573391 _91560 P Q). Qed.
Lemma lem3573393 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term663 _91307 _91560 t s f) = (term664 _91307 _91560 t s f).
Proof. exact (@lem3573392 _91560 (term295 _91307 _91560 t s f) (term327 _91307 _91560 t s f)). Qed.
Lemma lem3573394 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term665 _91307 _91560 t s f y) = (term286 _91307 _91560 t s f y).
Proof. exact (eq_refl (term665 _91307 _91560 t s f y)). Qed.
Lemma lem3573395 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term666 _91307 _91560 t s f) = (term295 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3573394 _91307 _91560 t s f y)). Qed.
Lemma lem3573396 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3573397 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term667 _91307 _91560 t s f) = (term296 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573396 _91560) (@lem3573395 _91307 _91560 t s f)). Qed.
Lemma lem3573398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3573399 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term668 _91307 _91560 t s f) = (term329 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573398) (@lem3573397 _91307 _91560 t s f)). Qed.
Lemma lem3573400 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term327 _91307 _91560 t s f) = (term327 _91307 _91560 t s f).
Proof. exact (eq_refl (term327 _91307 _91560 t s f)). Qed.
Lemma lem3573401 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term663 _91307 _91560 t s f) = (term331 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573399 _91307 _91560 t s f) (@lem3573400 _91307 _91560 t s f)). Qed.
Lemma lem3573402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573403 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term669 _91307 _91560 t s f) = (term670 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573402) (@lem3573401 _91307 _91560 t s f)). Qed.
Lemma lem3573404 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term665 _91307 _91560 t s f y) = (term286 _91307 _91560 t s f y).
Proof. exact (eq_refl (term665 _91307 _91560 t s f y)). Qed.
Lemma lem3573405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3573406 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term671 _91307 _91560 t s f y) = (term672 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3573405) (@lem3573404 _91307 _91560 t s f y)). Qed.
Lemma lem3573407 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term327 _91307 _91560 t s f) = (term327 _91307 _91560 t s f).
Proof. exact (eq_refl (term327 _91307 _91560 t s f)). Qed.
Lemma lem3573408 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term673 _91307 _91560 y t s f) = (term674 _91307 _91560 y t s f).
Proof. exact (MK_COMB (@lem3573406 _91307 _91560 t s f y) (@lem3573407 _91307 _91560 t s f)). Qed.
Lemma lem3573409 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term675 _91307 _91560 t s f) = (term676 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3573408 _91307 _91560 y t s f)). Qed.
Lemma lem3573410 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3573411 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term664 _91307 _91560 t s f) = (term677 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573410 _91560) (@lem3573409 _91307 _91560 t s f)). Qed.
Lemma lem3573412 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term663 _91307 _91560 t s f) = (term664 _91307 _91560 t s f)) = ((term331 _91307 _91560 t s f) = (term677 _91307 _91560 t s f)).
Proof. exact (MK_COMB (@lem3573403 _91307 _91560 t s f) (@lem3573411 _91307 _91560 t s f)). Qed.
Lemma lem3573413 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term331 _91307 _91560 t s f) = (term677 _91307 _91560 t s f).
Proof. exact (EQ_MP (@lem3573412 _91307 _91560 t s f) (@lem3573393 _91307 _91560 t s f)). Qed.
Lemma lem3573415 {A : Type'} (P : Prop) (Q : A -> Prop) : (term241 A P Q) = (term242 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3573416 {_91307 _91560 : Type'} (P : Prop) (Q : type805 _91307 _91560) : (term678 _91307 _91560 P Q) = (term679 _91307 _91560 P Q).
Proof. exact (@lem3573415 (_91560 -> _91307) P Q). Qed.
Lemma lem3573417 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term680 _91307 _91560 y t s f) = (term681 _91307 _91560 y t s f).
Proof. exact (@lem3573416 _91307 _91560 (term286 _91307 _91560 t s f y) (term326 _91307 _91560 t s f)). Qed.
Lemma lem3573418 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term477 _91307 _91560 t s f g) = (term316 _91307 _91560 t s f g).
Proof. exact (eq_refl (term477 _91307 _91560 t s f g)). Qed.
Lemma lem3573419 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term478 _91307 _91560 t s f) = (term326 _91307 _91560 t s f).
Proof. exact (fun_ext (fun g : _91560 -> _91307 => @lem3573418 _91307 _91560 t s f g)). Qed.
Lemma lem3573420 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3573421 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term479 _91307 _91560 t s f) = (term327 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573420 _91307 _91560) (@lem3573419 _91307 _91560 t s f)). Qed.
Lemma lem3573422 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term672 _91307 _91560 t s f y) = (term672 _91307 _91560 t s f y).
Proof. exact (eq_refl (term672 _91307 _91560 t s f y)). Qed.
Lemma lem3573423 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term680 _91307 _91560 y t s f) = (term674 _91307 _91560 y t s f).
Proof. exact (MK_COMB (@lem3573422 _91307 _91560 t s f y) (@lem3573421 _91307 _91560 t s f)). Qed.
Lemma lem3573424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573425 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term682 _91307 _91560 y t s f) = (term683 _91307 _91560 y t s f).
Proof. exact (MK_COMB (@lem3573424) (@lem3573423 _91307 _91560 y t s f)). Qed.
Lemma lem3573426 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term477 _91307 _91560 t s f g) = (term316 _91307 _91560 t s f g).
Proof. exact (eq_refl (term477 _91307 _91560 t s f g)). Qed.
Lemma lem3573427 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term672 _91307 _91560 t s f y) = (term672 _91307 _91560 t s f y).
Proof. exact (eq_refl (term672 _91307 _91560 t s f y)). Qed.
Lemma lem3573428 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term684 _91307 _91560 y t s f g) = (term685 _91307 _91560 y t s f g).
Proof. exact (MK_COMB (@lem3573427 _91307 _91560 t s f y) (@lem3573426 _91307 _91560 t s f g)). Qed.
Lemma lem3573429 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term686 _91307 _91560 y t s f) = (term687 _91307 _91560 y t s f).
Proof. exact (fun_ext (fun g : _91560 -> _91307 => @lem3573428 _91307 _91560 y t s f g)). Qed.
Lemma lem3573430 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3573431 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term681 _91307 _91560 y t s f) = (term688 _91307 _91560 y t s f).
Proof. exact (MK_COMB (@lem3573430 _91307 _91560) (@lem3573429 _91307 _91560 y t s f)). Qed.
Lemma lem3573432 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term680 _91307 _91560 y t s f) = (term681 _91307 _91560 y t s f)) = ((term674 _91307 _91560 y t s f) = (term688 _91307 _91560 y t s f)).
Proof. exact (MK_COMB (@lem3573425 _91307 _91560 y t s f) (@lem3573431 _91307 _91560 y t s f)). Qed.
Lemma lem3573433 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term674 _91307 _91560 y t s f) = (term688 _91307 _91560 y t s f).
Proof. exact (EQ_MP (@lem3573432 _91307 _91560 y t s f) (@lem3573417 _91307 _91560 y t s f)). Qed.
Lemma lem3573434 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term676 _91307 _91560 t s f) = (term689 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3573433 _91307 _91560 y t s f)). Qed.
Lemma lem3573435 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3573436 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term677 _91307 _91560 t s f) = (term690 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573435 _91560) (@lem3573434 _91307 _91560 t s f)). Qed.
Lemma lem3573437 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term331 _91307 _91560 t s f) = (term690 _91307 _91560 t s f).
Proof. exact (TRANS (@lem3573413 _91307 _91560 t s f) (@lem3573436 _91307 _91560 t s f)). Qed.
Lemma lem3573438 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term353 _91307 _91560 s f) = (term691 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573437 _91307 _91560 t s f)). Qed.
Lemma lem3573439 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573440 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term368 _91307 _91560 s f) = (term692 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573439 _91560) (@lem3573438 _91307 _91560 s f)). Qed.
Lemma lem3573442 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573443 {_91560 : Type'} (P : type672 _91560) : (term693 _91560 P) = (term694 _91560 P).
Proof. exact (@lem3573442 (_91560 -> Prop) _91560 P). Qed.
Lemma lem3573444 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term695 _91307 _91560 s f) = (term696 _91307 _91560 s f).
Proof. exact (@lem3573443 _91560 (term697 _91307 _91560 s f)). Qed.
Lemma lem3573445 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term698 _91307 _91560 s f t) = (term689 _91307 _91560 t s f).
Proof. exact (eq_refl (term698 _91307 _91560 s f t)). Qed.
Lemma lem3573446 {_91560 : Type'} (y : _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3573447 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (y : _91560) : (term699 _91307 _91560 s f t y) = (term700 _91307 _91560 t s f y).
Proof. exact (MK_COMB (@lem3573445 _91307 _91560 t s f) (@lem3573446 _91560 y)). Qed.
Lemma lem3573448 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term700 _91307 _91560 t s f y) = (term688 _91307 _91560 y t s f).
Proof. exact (eq_refl (term700 _91307 _91560 t s f y)). Qed.
Lemma lem3573449 {_91307 _91560 : Type'} (y : _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term699 _91307 _91560 s f t y) = (term688 _91307 _91560 y t s f).
Proof. exact (TRANS (@lem3573447 _91307 _91560 t s f y) (@lem3573448 _91307 _91560 y t s f)). Qed.
Lemma lem3573450 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term701 _91307 _91560 s f t) = (term689 _91307 _91560 t s f).
Proof. exact (fun_ext (fun y : _91560 => @lem3573449 _91307 _91560 y t s f)). Qed.
Lemma lem3573451 {_91560 : Type'} : (@ex _91560) = (@ex _91560).
Proof. exact (eq_refl (@ex _91560)). Qed.
Lemma lem3573452 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term702 _91307 _91560 s f t) = (term690 _91307 _91560 t s f).
Proof. exact (MK_COMB (@lem3573451 _91560) (@lem3573450 _91307 _91560 t s f)). Qed.
Lemma lem3573453 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term703 _91307 _91560 s f) = (term691 _91307 _91560 s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573452 _91307 _91560 t s f)). Qed.
Lemma lem3573454 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573455 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term695 _91307 _91560 s f) = (term692 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573454 _91560) (@lem3573453 _91307 _91560 s f)). Qed.
Lemma lem3573456 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573457 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term704 _91307 _91560 s f) = (term705 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573456) (@lem3573455 _91307 _91560 s f)). Qed.
Lemma lem3573458 {_91307 _91560 : Type'} (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term698 _91307 _91560 s f t) = (term689 _91307 _91560 t s f).
Proof. exact (eq_refl (term698 _91307 _91560 s f t)). Qed.
Lemma lem3573459 {_91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) : (y t) = (y t).
Proof. exact (eq_refl (y t)). Qed.
Lemma lem3573460 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type684 _91560) (t : _91560 -> Prop) : (term706 _91307 _91560 s f y t) = (term707 _91307 _91560 s f y t).
Proof. exact (MK_COMB (@lem3573458 _91307 _91560 t s f) (@lem3573459 _91560 y t)). Qed.
Lemma lem3573461 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term707 _91307 _91560 s f y t) = (term708 _91307 _91560 y t s f).
Proof. exact (eq_refl (term707 _91307 _91560 s f y t)). Qed.
Lemma lem3573462 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term706 _91307 _91560 s f y t) = (term708 _91307 _91560 y t s f).
Proof. exact (TRANS (@lem3573460 _91307 _91560 s f y t) (@lem3573461 _91307 _91560 y t s f)). Qed.
Lemma lem3573463 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term709 _91307 _91560 s f y) = (term710 _91307 _91560 y s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573462 _91307 _91560 y t s f)). Qed.
Lemma lem3573464 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573465 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term711 _91307 _91560 s f y) = (term712 _91307 _91560 y s f).
Proof. exact (MK_COMB (@lem3573464 _91560) (@lem3573463 _91307 _91560 y s f)). Qed.
Lemma lem3573466 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term713 _91307 _91560 s f) = (term714 _91307 _91560 s f).
Proof. exact (fun_ext (fun y : type684 _91560 => @lem3573465 _91307 _91560 y s f)). Qed.
Lemma lem3573467 {_91560 : Type'} : (@ex ((_91560 -> Prop) -> _91560)) = (@ex ((_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573468 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term696 _91307 _91560 s f) = (term715 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573467 _91560) (@lem3573466 _91307 _91560 s f)). Qed.
Lemma lem3573469 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term695 _91307 _91560 s f) = (term696 _91307 _91560 s f)) = ((term692 _91307 _91560 s f) = (term715 _91307 _91560 s f)).
Proof. exact (MK_COMB (@lem3573457 _91307 _91560 s f) (@lem3573468 _91307 _91560 s f)). Qed.
Lemma lem3573470 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term692 _91307 _91560 s f) = (term715 _91307 _91560 s f).
Proof. exact (EQ_MP (@lem3573469 _91307 _91560 s f) (@lem3573444 _91307 _91560 s f)). Qed.
Lemma lem3573472 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573473 {_91307 _91560 : Type'} (P : type856 _91307 _91560) : (term508 _91307 _91560 P) = (term509 _91307 _91560 P).
Proof. exact (@lem3573472 (_91560 -> Prop) (_91560 -> _91307) P). Qed.
Lemma lem3573474 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term716 _91307 _91560 y s f) = (term717 _91307 _91560 y s f).
Proof. exact (@lem3573473 _91307 _91560 (term718 _91307 _91560 y s f)). Qed.
Lemma lem3573475 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term719 _91307 _91560 y s f t) = (term720 _91307 _91560 y t s f).
Proof. exact (eq_refl (term719 _91307 _91560 y s f t)). Qed.
Lemma lem3573476 {_91307 _91560 : Type'} (g : _91560 -> _91307) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3573477 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term721 _91307 _91560 y s f t g) = (term722 _91307 _91560 y t s f g).
Proof. exact (MK_COMB (@lem3573475 _91307 _91560 y t s f) (@lem3573476 _91307 _91560 g)). Qed.
Lemma lem3573478 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term722 _91307 _91560 y t s f g) = (term723 _91307 _91560 y t s f g).
Proof. exact (eq_refl (term722 _91307 _91560 y t s f g)). Qed.
Lemma lem3573479 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : _91560 -> _91307) : (term721 _91307 _91560 y s f t g) = (term723 _91307 _91560 y t s f g).
Proof. exact (TRANS (@lem3573477 _91307 _91560 y t s f g) (@lem3573478 _91307 _91560 y t s f g)). Qed.
Lemma lem3573480 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term724 _91307 _91560 y s f t) = (term720 _91307 _91560 y t s f).
Proof. exact (fun_ext (fun g : _91560 -> _91307 => @lem3573479 _91307 _91560 y t s f g)). Qed.
Lemma lem3573481 {_91307 _91560 : Type'} : (@ex (_91560 -> _91307)) = (@ex (_91560 -> _91307)).
Proof. exact (eq_refl (@ex (_91560 -> _91307))). Qed.
Lemma lem3573482 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term725 _91307 _91560 y s f t) = (term708 _91307 _91560 y t s f).
Proof. exact (MK_COMB (@lem3573481 _91307 _91560) (@lem3573480 _91307 _91560 y t s f)). Qed.
Lemma lem3573483 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term726 _91307 _91560 y s f) = (term710 _91307 _91560 y s f).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573482 _91307 _91560 y t s f)). Qed.
Lemma lem3573484 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573485 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term716 _91307 _91560 y s f) = (term712 _91307 _91560 y s f).
Proof. exact (MK_COMB (@lem3573484 _91560) (@lem3573483 _91307 _91560 y s f)). Qed.
Lemma lem3573486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573487 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term727 _91307 _91560 y s f) = (term728 _91307 _91560 y s f).
Proof. exact (MK_COMB (@lem3573486) (@lem3573485 _91307 _91560 y s f)). Qed.
Lemma lem3573488 {_91307 _91560 : Type'} (y : type684 _91560) (t : _91560 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term719 _91307 _91560 y s f t) = (term720 _91307 _91560 y t s f).
Proof. exact (eq_refl (term719 _91307 _91560 y s f t)). Qed.
Lemma lem3573489 {_91307 _91560 : Type'} (g : type861 _91307 _91560) (t : _91560 -> Prop) : (g t) = (g t).
Proof. exact (eq_refl (g t)). Qed.
Lemma lem3573490 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : type861 _91307 _91560) (t : _91560 -> Prop) : (term729 _91307 _91560 y s f g t) = (term730 _91307 _91560 y s f g t).
Proof. exact (MK_COMB (@lem3573488 _91307 _91560 y t s f) (@lem3573489 _91307 _91560 g t)). Qed.
Lemma lem3573491 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : type861 _91307 _91560) (t : _91560 -> Prop) : (term730 _91307 _91560 y s f g t) = (term731 _91307 _91560 y s f g t).
Proof. exact (eq_refl (term730 _91307 _91560 y s f g t)). Qed.
Lemma lem3573492 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : type861 _91307 _91560) (t : _91560 -> Prop) : (term729 _91307 _91560 y s f g t) = (term731 _91307 _91560 y s f g t).
Proof. exact (TRANS (@lem3573490 _91307 _91560 y s f g t) (@lem3573491 _91307 _91560 y s f g t)). Qed.
Lemma lem3573493 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : type861 _91307 _91560) : (term732 _91307 _91560 y s f g) = (term733 _91307 _91560 y s f g).
Proof. exact (fun_ext (fun t : _91560 -> Prop => @lem3573492 _91307 _91560 y s f g t)). Qed.
Lemma lem3573494 {_91560 : Type'} : (@all (_91560 -> Prop)) = (@all (_91560 -> Prop)).
Proof. exact (eq_refl (@all (_91560 -> Prop))). Qed.
Lemma lem3573495 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : type861 _91307 _91560) : (term734 _91307 _91560 y s f g) = (term735 _91307 _91560 y s f g).
Proof. exact (MK_COMB (@lem3573494 _91560) (@lem3573493 _91307 _91560 y s f g)). Qed.
Lemma lem3573496 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term736 _91307 _91560 y s f) = (term737 _91307 _91560 y s f).
Proof. exact (fun_ext (fun g : type861 _91307 _91560 => @lem3573495 _91307 _91560 y s f g)). Qed.
Lemma lem3573497 {_91307 _91560 : Type'} : (@ex ((_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573498 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term717 _91307 _91560 y s f) = (term738 _91307 _91560 y s f).
Proof. exact (MK_COMB (@lem3573497 _91307 _91560) (@lem3573496 _91307 _91560 y s f)). Qed.
Lemma lem3573499 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : ((term716 _91307 _91560 y s f) = (term717 _91307 _91560 y s f)) = ((term712 _91307 _91560 y s f) = (term738 _91307 _91560 y s f)).
Proof. exact (MK_COMB (@lem3573487 _91307 _91560 y s f) (@lem3573498 _91307 _91560 y s f)). Qed.
Lemma lem3573500 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term712 _91307 _91560 y s f) = (term738 _91307 _91560 y s f).
Proof. exact (EQ_MP (@lem3573499 _91307 _91560 y s f) (@lem3573474 _91307 _91560 y s f)). Qed.
Lemma lem3573501 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term714 _91307 _91560 s f) = (term739 _91307 _91560 s f).
Proof. exact (fun_ext (fun y : type684 _91560 => @lem3573500 _91307 _91560 y s f)). Qed.
Lemma lem3573502 {_91560 : Type'} : (@ex ((_91560 -> Prop) -> _91560)) = (@ex ((_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573503 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term715 _91307 _91560 s f) = (term740 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573502 _91560) (@lem3573501 _91307 _91560 s f)). Qed.
Lemma lem3573504 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term692 _91307 _91560 s f) = (term740 _91307 _91560 s f).
Proof. exact (TRANS (@lem3573470 _91307 _91560 s f) (@lem3573503 _91307 _91560 s f)). Qed.
Lemma lem3573505 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term368 _91307 _91560 s f) = (term740 _91307 _91560 s f).
Proof. exact (TRANS (@lem3573440 _91307 _91560 s f) (@lem3573504 _91307 _91560 s f)). Qed.
Lemma lem3573506 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term377 _91307 _91560 s) = (term741 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573505 _91307 _91560 s f)). Qed.
Lemma lem3573507 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573508 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term392 _91307 _91560 s) = (term742 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573507 _91307 _91560) (@lem3573506 _91307 _91560 s)). Qed.
Lemma lem3573510 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573511 {_91307 _91560 : Type'} (P : type508 _91307 _91560) : (term743 _91307 _91560 P) = (term744 _91307 _91560 P).
Proof. exact (@lem3573510 (_91307 -> _91560) (type684 _91560) P). Qed.
Lemma lem3573512 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term745 _91307 _91560 s) = (term746 _91307 _91560 s).
Proof. exact (@lem3573511 _91307 _91560 (term747 _91307 _91560 s)). Qed.
Lemma lem3573513 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term748 _91307 _91560 s f) = (term739 _91307 _91560 s f).
Proof. exact (eq_refl (term748 _91307 _91560 s f)). Qed.
Lemma lem3573514 {_91560 : Type'} (y : type684 _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3573515 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) (y : type684 _91560) : (term749 _91307 _91560 s f y) = (term750 _91307 _91560 s f y).
Proof. exact (MK_COMB (@lem3573513 _91307 _91560 s f) (@lem3573514 _91560 y)). Qed.
Lemma lem3573516 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term750 _91307 _91560 s f y) = (term738 _91307 _91560 y s f).
Proof. exact (eq_refl (term750 _91307 _91560 s f y)). Qed.
Lemma lem3573517 {_91307 _91560 : Type'} (y : type684 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term749 _91307 _91560 s f y) = (term738 _91307 _91560 y s f).
Proof. exact (TRANS (@lem3573515 _91307 _91560 s f y) (@lem3573516 _91307 _91560 y s f)). Qed.
Lemma lem3573518 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term751 _91307 _91560 s f) = (term739 _91307 _91560 s f).
Proof. exact (fun_ext (fun y : type684 _91560 => @lem3573517 _91307 _91560 y s f)). Qed.
Lemma lem3573519 {_91560 : Type'} : (@ex ((_91560 -> Prop) -> _91560)) = (@ex ((_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573520 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term752 _91307 _91560 s f) = (term740 _91307 _91560 s f).
Proof. exact (MK_COMB (@lem3573519 _91560) (@lem3573518 _91307 _91560 s f)). Qed.
Lemma lem3573521 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term753 _91307 _91560 s) = (term741 _91307 _91560 s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573520 _91307 _91560 s f)). Qed.
Lemma lem3573522 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573523 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term745 _91307 _91560 s) = (term742 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573522 _91307 _91560) (@lem3573521 _91307 _91560 s)). Qed.
Lemma lem3573524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573525 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term754 _91307 _91560 s) = (term755 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573524) (@lem3573523 _91307 _91560 s)). Qed.
Lemma lem3573526 {_91307 _91560 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91560) : (term748 _91307 _91560 s f) = (term739 _91307 _91560 s f).
Proof. exact (eq_refl (term748 _91307 _91560 s f)). Qed.
Lemma lem3573527 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (f : _91307 -> _91560) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3573528 {_91307 _91560 : Type'} (s : _91307 -> Prop) (y : type533 _91307 _91560) (f : _91307 -> _91560) : (term756 _91307 _91560 s y f) = (term757 _91307 _91560 s y f).
Proof. exact (MK_COMB (@lem3573526 _91307 _91560 s f) (@lem3573527 _91307 _91560 y f)). Qed.
Lemma lem3573529 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term757 _91307 _91560 s y f) = (term758 _91307 _91560 y s f).
Proof. exact (eq_refl (term757 _91307 _91560 s y f)). Qed.
Lemma lem3573530 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term756 _91307 _91560 s y f) = (term758 _91307 _91560 y s f).
Proof. exact (TRANS (@lem3573528 _91307 _91560 s y f) (@lem3573529 _91307 _91560 y s f)). Qed.
Lemma lem3573531 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term759 _91307 _91560 s y) = (term760 _91307 _91560 y s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573530 _91307 _91560 y s f)). Qed.
Lemma lem3573532 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573533 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term761 _91307 _91560 s y) = (term762 _91307 _91560 y s).
Proof. exact (MK_COMB (@lem3573532 _91307 _91560) (@lem3573531 _91307 _91560 y s)). Qed.
Lemma lem3573534 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term763 _91307 _91560 s) = (term764 _91307 _91560 s).
Proof. exact (fun_ext (fun y : type533 _91307 _91560 => @lem3573533 _91307 _91560 y s)). Qed.
Lemma lem3573535 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573536 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term746 _91307 _91560 s) = (term765 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573535 _91307 _91560) (@lem3573534 _91307 _91560 s)). Qed.
Lemma lem3573537 {_91307 _91560 : Type'} (s : _91307 -> Prop) : ((term745 _91307 _91560 s) = (term746 _91307 _91560 s)) = ((term742 _91307 _91560 s) = (term765 _91307 _91560 s)).
Proof. exact (MK_COMB (@lem3573525 _91307 _91560 s) (@lem3573536 _91307 _91560 s)). Qed.
Lemma lem3573538 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term742 _91307 _91560 s) = (term765 _91307 _91560 s).
Proof. exact (EQ_MP (@lem3573537 _91307 _91560 s) (@lem3573512 _91307 _91560 s)). Qed.
Lemma lem3573540 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573541 {_91307 _91560 : Type'} (P : type507 _91307 _91560) : (term560 _91307 _91560 P) = (term561 _91307 _91560 P).
Proof. exact (@lem3573540 (_91307 -> _91560) (type861 _91307 _91560) P). Qed.
Lemma lem3573542 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term766 _91307 _91560 y s) = (term767 _91307 _91560 y s).
Proof. exact (@lem3573541 _91307 _91560 (term768 _91307 _91560 y s)). Qed.
Lemma lem3573543 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term769 _91307 _91560 y s f) = (term770 _91307 _91560 y s f).
Proof. exact (eq_refl (term769 _91307 _91560 y s f)). Qed.
Lemma lem3573544 {_91307 _91560 : Type'} (g : type861 _91307 _91560) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3573545 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : type861 _91307 _91560) : (term771 _91307 _91560 y s f g) = (term772 _91307 _91560 y s f g).
Proof. exact (MK_COMB (@lem3573543 _91307 _91560 y s f) (@lem3573544 _91307 _91560 g)). Qed.
Lemma lem3573546 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : type861 _91307 _91560) : (term772 _91307 _91560 y s f g) = (term773 _91307 _91560 y s f g).
Proof. exact (eq_refl (term772 _91307 _91560 y s f g)). Qed.
Lemma lem3573547 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) (g : type861 _91307 _91560) : (term771 _91307 _91560 y s f g) = (term773 _91307 _91560 y s f g).
Proof. exact (TRANS (@lem3573545 _91307 _91560 y s f g) (@lem3573546 _91307 _91560 y s f g)). Qed.
Lemma lem3573548 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term774 _91307 _91560 y s f) = (term770 _91307 _91560 y s f).
Proof. exact (fun_ext (fun g : type861 _91307 _91560 => @lem3573547 _91307 _91560 y s f g)). Qed.
Lemma lem3573549 {_91307 _91560 : Type'} : (@ex ((_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573550 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term775 _91307 _91560 y s f) = (term758 _91307 _91560 y s f).
Proof. exact (MK_COMB (@lem3573549 _91307 _91560) (@lem3573548 _91307 _91560 y s f)). Qed.
Lemma lem3573551 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term776 _91307 _91560 y s) = (term760 _91307 _91560 y s).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573550 _91307 _91560 y s f)). Qed.
Lemma lem3573552 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573553 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term766 _91307 _91560 y s) = (term762 _91307 _91560 y s).
Proof. exact (MK_COMB (@lem3573552 _91307 _91560) (@lem3573551 _91307 _91560 y s)). Qed.
Lemma lem3573554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573555 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term777 _91307 _91560 y s) = (term778 _91307 _91560 y s).
Proof. exact (MK_COMB (@lem3573554) (@lem3573553 _91307 _91560 y s)). Qed.
Lemma lem3573556 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (f : _91307 -> _91560) : (term769 _91307 _91560 y s f) = (term770 _91307 _91560 y s f).
Proof. exact (eq_refl (term769 _91307 _91560 y s f)). Qed.
Lemma lem3573557 {_91307 _91560 : Type'} (g : type532 _91307 _91560) (f : _91307 -> _91560) : (g f) = (g f).
Proof. exact (eq_refl (g f)). Qed.
Lemma lem3573558 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (g : type532 _91307 _91560) (f : _91307 -> _91560) : (term779 _91307 _91560 y s g f) = (term780 _91307 _91560 y s g f).
Proof. exact (MK_COMB (@lem3573556 _91307 _91560 y s f) (@lem3573557 _91307 _91560 g f)). Qed.
Lemma lem3573559 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (g : type532 _91307 _91560) (f : _91307 -> _91560) : (term780 _91307 _91560 y s g f) = (term781 _91307 _91560 y s g f).
Proof. exact (eq_refl (term780 _91307 _91560 y s g f)). Qed.
Lemma lem3573560 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (g : type532 _91307 _91560) (f : _91307 -> _91560) : (term779 _91307 _91560 y s g f) = (term781 _91307 _91560 y s g f).
Proof. exact (TRANS (@lem3573558 _91307 _91560 y s g f) (@lem3573559 _91307 _91560 y s g f)). Qed.
Lemma lem3573561 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (g : type532 _91307 _91560) : (term782 _91307 _91560 y s g) = (term783 _91307 _91560 y s g).
Proof. exact (fun_ext (fun f : _91307 -> _91560 => @lem3573560 _91307 _91560 y s g f)). Qed.
Lemma lem3573562 {_91307 _91560 : Type'} : (@all (_91307 -> _91560)) = (@all (_91307 -> _91560)).
Proof. exact (eq_refl (@all (_91307 -> _91560))). Qed.
Lemma lem3573563 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) (g : type532 _91307 _91560) : (term784 _91307 _91560 y s g) = (term785 _91307 _91560 y s g).
Proof. exact (MK_COMB (@lem3573562 _91307 _91560) (@lem3573561 _91307 _91560 y s g)). Qed.
Lemma lem3573564 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term786 _91307 _91560 y s) = (term787 _91307 _91560 y s).
Proof. exact (fun_ext (fun g : type532 _91307 _91560 => @lem3573563 _91307 _91560 y s g)). Qed.
Lemma lem3573565 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573566 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term767 _91307 _91560 y s) = (term788 _91307 _91560 y s).
Proof. exact (MK_COMB (@lem3573565 _91307 _91560) (@lem3573564 _91307 _91560 y s)). Qed.
Lemma lem3573567 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : ((term766 _91307 _91560 y s) = (term767 _91307 _91560 y s)) = ((term762 _91307 _91560 y s) = (term788 _91307 _91560 y s)).
Proof. exact (MK_COMB (@lem3573555 _91307 _91560 y s) (@lem3573566 _91307 _91560 y s)). Qed.
Lemma lem3573568 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term762 _91307 _91560 y s) = (term788 _91307 _91560 y s).
Proof. exact (EQ_MP (@lem3573567 _91307 _91560 y s) (@lem3573542 _91307 _91560 y s)). Qed.
Lemma lem3573569 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term764 _91307 _91560 s) = (term789 _91307 _91560 s).
Proof. exact (fun_ext (fun y : type533 _91307 _91560 => @lem3573568 _91307 _91560 y s)). Qed.
Lemma lem3573570 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573571 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term765 _91307 _91560 s) = (term790 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573570 _91307 _91560) (@lem3573569 _91307 _91560 s)). Qed.
Lemma lem3573572 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term742 _91307 _91560 s) = (term790 _91307 _91560 s).
Proof. exact (TRANS (@lem3573538 _91307 _91560 s) (@lem3573571 _91307 _91560 s)). Qed.
Lemma lem3573573 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term392 _91307 _91560 s) = (term790 _91307 _91560 s).
Proof. exact (TRANS (@lem3573508 _91307 _91560 s) (@lem3573572 _91307 _91560 s)). Qed.
Lemma lem3573574 {_91307 _91560 : Type'} : (term399 _91307 _91560) = (term791 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573573 _91307 _91560 s)). Qed.
Lemma lem3573575 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573576 {_91307 _91560 : Type'} : (term414 _91307 _91560) = (term792 _91307 _91560).
Proof. exact (MK_COMB (@lem3573575 _91307) (@lem3573574 _91307 _91560)). Qed.
Lemma lem3573578 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573579 {_91307 _91560 : Type'} (P : type592 _91307 _91560) : (term793 _91307 _91560 P) = (term794 _91307 _91560 P).
Proof. exact (@lem3573578 (_91307 -> Prop) (type533 _91307 _91560) P). Qed.
Lemma lem3573580 {_91307 _91560 : Type'} : (term795 _91307 _91560) = (term796 _91307 _91560).
Proof. exact (@lem3573579 _91307 _91560 (term797 _91307 _91560)). Qed.
Lemma lem3573581 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term798 _91307 _91560 s) = (term789 _91307 _91560 s).
Proof. exact (eq_refl (term798 _91307 _91560 s)). Qed.
Lemma lem3573582 {_91307 _91560 : Type'} (y : type533 _91307 _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3573583 {_91307 _91560 : Type'} (s : _91307 -> Prop) (y : type533 _91307 _91560) : (term799 _91307 _91560 s y) = (term800 _91307 _91560 s y).
Proof. exact (MK_COMB (@lem3573581 _91307 _91560 s) (@lem3573582 _91307 _91560 y)). Qed.
Lemma lem3573584 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term800 _91307 _91560 s y) = (term788 _91307 _91560 y s).
Proof. exact (eq_refl (term800 _91307 _91560 s y)). Qed.
Lemma lem3573585 {_91307 _91560 : Type'} (y : type533 _91307 _91560) (s : _91307 -> Prop) : (term799 _91307 _91560 s y) = (term788 _91307 _91560 y s).
Proof. exact (TRANS (@lem3573583 _91307 _91560 s y) (@lem3573584 _91307 _91560 y s)). Qed.
Lemma lem3573586 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term801 _91307 _91560 s) = (term789 _91307 _91560 s).
Proof. exact (fun_ext (fun y : type533 _91307 _91560 => @lem3573585 _91307 _91560 y s)). Qed.
Lemma lem3573587 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573588 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term802 _91307 _91560 s) = (term790 _91307 _91560 s).
Proof. exact (MK_COMB (@lem3573587 _91307 _91560) (@lem3573586 _91307 _91560 s)). Qed.
Lemma lem3573589 {_91307 _91560 : Type'} : (term803 _91307 _91560) = (term791 _91307 _91560).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573588 _91307 _91560 s)). Qed.
Lemma lem3573590 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573591 {_91307 _91560 : Type'} : (term795 _91307 _91560) = (term792 _91307 _91560).
Proof. exact (MK_COMB (@lem3573590 _91307) (@lem3573589 _91307 _91560)). Qed.
Lemma lem3573592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573593 {_91307 _91560 : Type'} : (term804 _91307 _91560) = (term805 _91307 _91560).
Proof. exact (MK_COMB (@lem3573592) (@lem3573591 _91307 _91560)). Qed.
Lemma lem3573594 {_91307 _91560 : Type'} (s : _91307 -> Prop) : (term798 _91307 _91560 s) = (term789 _91307 _91560 s).
Proof. exact (eq_refl (term798 _91307 _91560 s)). Qed.
Lemma lem3573595 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3573596 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) : (term806 _91307 _91560 y s) = (term807 _91307 _91560 y s).
Proof. exact (MK_COMB (@lem3573594 _91307 _91560 s) (@lem3573595 _91307 _91560 y s)). Qed.
Lemma lem3573597 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) : (term807 _91307 _91560 y s) = (term808 _91307 _91560 y s).
Proof. exact (eq_refl (term807 _91307 _91560 y s)). Qed.
Lemma lem3573598 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) : (term806 _91307 _91560 y s) = (term808 _91307 _91560 y s).
Proof. exact (TRANS (@lem3573596 _91307 _91560 y s) (@lem3573597 _91307 _91560 y s)). Qed.
Lemma lem3573599 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term809 _91307 _91560 y) = (term810 _91307 _91560 y).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573598 _91307 _91560 y s)). Qed.
Lemma lem3573600 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573601 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term811 _91307 _91560 y) = (term812 _91307 _91560 y).
Proof. exact (MK_COMB (@lem3573600 _91307) (@lem3573599 _91307 _91560 y)). Qed.
Lemma lem3573602 {_91307 _91560 : Type'} : (term813 _91307 _91560) = (term814 _91307 _91560).
Proof. exact (fun_ext (fun y : type630 _91307 _91560 => @lem3573601 _91307 _91560 y)). Qed.
Lemma lem3573603 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573604 {_91307 _91560 : Type'} : (term796 _91307 _91560) = (term815 _91307 _91560).
Proof. exact (MK_COMB (@lem3573603 _91307 _91560) (@lem3573602 _91307 _91560)). Qed.
Lemma lem3573605 {_91307 _91560 : Type'} : ((term795 _91307 _91560) = (term796 _91307 _91560)) = ((term792 _91307 _91560) = (term815 _91307 _91560)).
Proof. exact (MK_COMB (@lem3573593 _91307 _91560) (@lem3573604 _91307 _91560)). Qed.
Lemma lem3573606 {_91307 _91560 : Type'} : (term792 _91307 _91560) = (term815 _91307 _91560).
Proof. exact (EQ_MP (@lem3573605 _91307 _91560) (@lem3573580 _91307 _91560)). Qed.
Lemma lem3573608 {A B : Type'} (P : type1413 A B) : (term98 A B P) = (term99 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3573609 {_91307 _91560 : Type'} (P : type591 _91307 _91560) : (term612 _91307 _91560 P) = (term613 _91307 _91560 P).
Proof. exact (@lem3573608 (_91307 -> Prop) (type532 _91307 _91560) P). Qed.
Lemma lem3573610 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term816 _91307 _91560 y) = (term817 _91307 _91560 y).
Proof. exact (@lem3573609 _91307 _91560 (term818 _91307 _91560 y)). Qed.
Lemma lem3573611 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) : (term819 _91307 _91560 y s) = (term820 _91307 _91560 y s).
Proof. exact (eq_refl (term819 _91307 _91560 y s)). Qed.
Lemma lem3573612 {_91307 _91560 : Type'} (g : type532 _91307 _91560) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3573613 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) (g : type532 _91307 _91560) : (term821 _91307 _91560 y s g) = (term822 _91307 _91560 y s g).
Proof. exact (MK_COMB (@lem3573611 _91307 _91560 y s) (@lem3573612 _91307 _91560 g)). Qed.
Lemma lem3573614 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) (g : type532 _91307 _91560) : (term822 _91307 _91560 y s g) = (term823 _91307 _91560 y s g).
Proof. exact (eq_refl (term822 _91307 _91560 y s g)). Qed.
Lemma lem3573615 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) (g : type532 _91307 _91560) : (term821 _91307 _91560 y s g) = (term823 _91307 _91560 y s g).
Proof. exact (TRANS (@lem3573613 _91307 _91560 y s g) (@lem3573614 _91307 _91560 y s g)). Qed.
Lemma lem3573616 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) : (term824 _91307 _91560 y s) = (term820 _91307 _91560 y s).
Proof. exact (fun_ext (fun g : type532 _91307 _91560 => @lem3573615 _91307 _91560 y s g)). Qed.
Lemma lem3573617 {_91307 _91560 : Type'} : (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573618 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) : (term825 _91307 _91560 y s) = (term808 _91307 _91560 y s).
Proof. exact (MK_COMB (@lem3573617 _91307 _91560) (@lem3573616 _91307 _91560 y s)). Qed.
Lemma lem3573619 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term826 _91307 _91560 y) = (term810 _91307 _91560 y).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573618 _91307 _91560 y s)). Qed.
Lemma lem3573620 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573621 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term816 _91307 _91560 y) = (term812 _91307 _91560 y).
Proof. exact (MK_COMB (@lem3573620 _91307) (@lem3573619 _91307 _91560 y)). Qed.
Lemma lem3573622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573623 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term827 _91307 _91560 y) = (term828 _91307 _91560 y).
Proof. exact (MK_COMB (@lem3573622) (@lem3573621 _91307 _91560 y)). Qed.
Lemma lem3573624 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (s : _91307 -> Prop) : (term819 _91307 _91560 y s) = (term820 _91307 _91560 y s).
Proof. exact (eq_refl (term819 _91307 _91560 y s)). Qed.
Lemma lem3573625 {_91307 _91560 : Type'} (g : type629 _91307 _91560) (s : _91307 -> Prop) : (g s) = (g s).
Proof. exact (eq_refl (g s)). Qed.
Lemma lem3573626 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (g : type629 _91307 _91560) (s : _91307 -> Prop) : (term829 _91307 _91560 y g s) = (term830 _91307 _91560 y g s).
Proof. exact (MK_COMB (@lem3573624 _91307 _91560 y s) (@lem3573625 _91307 _91560 g s)). Qed.
Lemma lem3573627 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (g : type629 _91307 _91560) (s : _91307 -> Prop) : (term830 _91307 _91560 y g s) = (term831 _91307 _91560 y g s).
Proof. exact (eq_refl (term830 _91307 _91560 y g s)). Qed.
Lemma lem3573628 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (g : type629 _91307 _91560) (s : _91307 -> Prop) : (term829 _91307 _91560 y g s) = (term831 _91307 _91560 y g s).
Proof. exact (TRANS (@lem3573626 _91307 _91560 y g s) (@lem3573627 _91307 _91560 y g s)). Qed.
Lemma lem3573629 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (g : type629 _91307 _91560) : (term832 _91307 _91560 y g) = (term833 _91307 _91560 y g).
Proof. exact (fun_ext (fun s : _91307 -> Prop => @lem3573628 _91307 _91560 y g s)). Qed.
Lemma lem3573630 {_91307 : Type'} : (@all (_91307 -> Prop)) = (@all (_91307 -> Prop)).
Proof. exact (eq_refl (@all (_91307 -> Prop))). Qed.
Lemma lem3573631 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (g : type629 _91307 _91560) : (term834 _91307 _91560 y g) = (term835 _91307 _91560 y g).
Proof. exact (MK_COMB (@lem3573630 _91307) (@lem3573629 _91307 _91560 y g)). Qed.
Lemma lem3573632 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term836 _91307 _91560 y) = (term837 _91307 _91560 y).
Proof. exact (fun_ext (fun g : type629 _91307 _91560 => @lem3573631 _91307 _91560 y g)). Qed.
Lemma lem3573633 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573634 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term817 _91307 _91560 y) = (term838 _91307 _91560 y).
Proof. exact (MK_COMB (@lem3573633 _91307 _91560) (@lem3573632 _91307 _91560 y)). Qed.
Lemma lem3573635 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : ((term816 _91307 _91560 y) = (term817 _91307 _91560 y)) = ((term812 _91307 _91560 y) = (term838 _91307 _91560 y)).
Proof. exact (MK_COMB (@lem3573623 _91307 _91560 y) (@lem3573634 _91307 _91560 y)). Qed.
Lemma lem3573636 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term812 _91307 _91560 y) = (term838 _91307 _91560 y).
Proof. exact (EQ_MP (@lem3573635 _91307 _91560 y) (@lem3573610 _91307 _91560 y)). Qed.
Lemma lem3573637 {_91307 _91560 : Type'} : (term814 _91307 _91560) = (term839 _91307 _91560).
Proof. exact (fun_ext (fun y : type630 _91307 _91560 => @lem3573636 _91307 _91560 y)). Qed.
Lemma lem3573638 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573639 {_91307 _91560 : Type'} : (term815 _91307 _91560) = (term840 _91307 _91560).
Proof. exact (MK_COMB (@lem3573638 _91307 _91560) (@lem3573637 _91307 _91560)). Qed.
Lemma lem3573640 {_91307 _91560 : Type'} : (term792 _91307 _91560) = (term840 _91307 _91560).
Proof. exact (TRANS (@lem3573606 _91307 _91560) (@lem3573639 _91307 _91560)). Qed.
Lemma lem3573641 {_91307 _91560 : Type'} : (term414 _91307 _91560) = (term840 _91307 _91560).
Proof. exact (TRANS (@lem3573576 _91307 _91560) (@lem3573640 _91307 _91560)). Qed.
Lemma lem3573642 {_91307 _91560 : Type'} : (term415 _91307 _91560) = (term841 _91307 _91560).
Proof. exact (MK_COMB (@lem3573387 _91307 _91560) (@lem3573641 _91307 _91560)). Qed.
Lemma lem3573644 {A : Type'} (P : A -> Prop) (Q : Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3573645 {_91307 _91560 : Type'} (P : type134 _91307 _91560) (Q : Prop) : (term842 _91307 _91560 P Q) = (term843 _91307 _91560 P Q).
Proof. exact (@lem3573644 (type629 _91307 _91560) P Q). Qed.
Lemma lem3573646 {_91307 _91560 : Type'} : (term844 _91307 _91560) = (term845 _91307 _91560).
Proof. exact (@lem3573645 _91307 _91560 (term660 _91307 _91560) (term840 _91307 _91560)). Qed.
Lemma lem3573647 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term846 _91307 _91560 x) = (term659 _91307 _91560 x).
Proof. exact (eq_refl (term846 _91307 _91560 x)). Qed.
Lemma lem3573648 {_91307 _91560 : Type'} : (term847 _91307 _91560) = (term660 _91307 _91560).
Proof. exact (fun_ext (fun x : type629 _91307 _91560 => @lem3573647 _91307 _91560 x)). Qed.
Lemma lem3573649 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573650 {_91307 _91560 : Type'} : (term848 _91307 _91560) = (term661 _91307 _91560).
Proof. exact (MK_COMB (@lem3573649 _91307 _91560) (@lem3573648 _91307 _91560)). Qed.
Lemma lem3573651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3573652 {_91307 _91560 : Type'} : (term849 _91307 _91560) = (term662 _91307 _91560).
Proof. exact (MK_COMB (@lem3573651) (@lem3573650 _91307 _91560)). Qed.
Lemma lem3573653 {_91307 _91560 : Type'} : (term840 _91307 _91560) = (term840 _91307 _91560).
Proof. exact (eq_refl (term840 _91307 _91560)). Qed.
Lemma lem3573654 {_91307 _91560 : Type'} : (term844 _91307 _91560) = (term841 _91307 _91560).
Proof. exact (MK_COMB (@lem3573652 _91307 _91560) (@lem3573653 _91307 _91560)). Qed.
Lemma lem3573655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573656 {_91307 _91560 : Type'} : (term850 _91307 _91560) = (term851 _91307 _91560).
Proof. exact (MK_COMB (@lem3573655) (@lem3573654 _91307 _91560)). Qed.
Lemma lem3573657 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term846 _91307 _91560 x) = (term659 _91307 _91560 x).
Proof. exact (eq_refl (term846 _91307 _91560 x)). Qed.
Lemma lem3573658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3573659 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term852 _91307 _91560 x) = (term853 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573658) (@lem3573657 _91307 _91560 x)). Qed.
Lemma lem3573660 {_91307 _91560 : Type'} : (term840 _91307 _91560) = (term840 _91307 _91560).
Proof. exact (eq_refl (term840 _91307 _91560)). Qed.
Lemma lem3573661 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term854 _91307 _91560 x) = (term855 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573659 _91307 _91560 x) (@lem3573660 _91307 _91560)). Qed.
Lemma lem3573662 {_91307 _91560 : Type'} : (term856 _91307 _91560) = (term857 _91307 _91560).
Proof. exact (fun_ext (fun x : type629 _91307 _91560 => @lem3573661 _91307 _91560 x)). Qed.
Lemma lem3573663 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573664 {_91307 _91560 : Type'} : (term845 _91307 _91560) = (term858 _91307 _91560).
Proof. exact (MK_COMB (@lem3573663 _91307 _91560) (@lem3573662 _91307 _91560)). Qed.
Lemma lem3573665 {_91307 _91560 : Type'} : ((term844 _91307 _91560) = (term845 _91307 _91560)) = ((term841 _91307 _91560) = (term858 _91307 _91560)).
Proof. exact (MK_COMB (@lem3573656 _91307 _91560) (@lem3573664 _91307 _91560)). Qed.
Lemma lem3573666 {_91307 _91560 : Type'} : (term841 _91307 _91560) = (term858 _91307 _91560).
Proof. exact (EQ_MP (@lem3573665 _91307 _91560) (@lem3573646 _91307 _91560)). Qed.
Lemma lem3573668 {A : Type'} (P : A -> Prop) (Q : Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3573669 {_91307 _91560 : Type'} (P : type133 _91307 _91560) (Q : Prop) : (term859 _91307 _91560 P Q) = (term860 _91307 _91560 P Q).
Proof. exact (@lem3573668 (type628 _91307 _91560) P Q). Qed.
Lemma lem3573670 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term861 _91307 _91560 x) = (term862 _91307 _91560 x).
Proof. exact (@lem3573669 _91307 _91560 (term658 _91307 _91560 x) (term840 _91307 _91560)). Qed.
Lemma lem3573671 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term863 _91307 _91560 x y) = (term656 _91307 _91560 x y).
Proof. exact (eq_refl (term863 _91307 _91560 x y)). Qed.
Lemma lem3573672 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term864 _91307 _91560 x) = (term658 _91307 _91560 x).
Proof. exact (fun_ext (fun y : type628 _91307 _91560 => @lem3573671 _91307 _91560 x y)). Qed.
Lemma lem3573673 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573674 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term865 _91307 _91560 x) = (term659 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573673 _91307 _91560) (@lem3573672 _91307 _91560 x)). Qed.
Lemma lem3573675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3573676 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term866 _91307 _91560 x) = (term853 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573675) (@lem3573674 _91307 _91560 x)). Qed.
Lemma lem3573677 {_91307 _91560 : Type'} : (term840 _91307 _91560) = (term840 _91307 _91560).
Proof. exact (eq_refl (term840 _91307 _91560)). Qed.
Lemma lem3573678 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term861 _91307 _91560 x) = (term855 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573676 _91307 _91560 x) (@lem3573677 _91307 _91560)). Qed.
Lemma lem3573679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573680 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term867 _91307 _91560 x) = (term868 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573679) (@lem3573678 _91307 _91560 x)). Qed.
Lemma lem3573681 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term863 _91307 _91560 x y) = (term656 _91307 _91560 x y).
Proof. exact (eq_refl (term863 _91307 _91560 x y)). Qed.
Lemma lem3573682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3573683 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term869 _91307 _91560 x y) = (term870 _91307 _91560 x y).
Proof. exact (MK_COMB (@lem3573682) (@lem3573681 _91307 _91560 x y)). Qed.
Lemma lem3573684 {_91307 _91560 : Type'} : (term840 _91307 _91560) = (term840 _91307 _91560).
Proof. exact (eq_refl (term840 _91307 _91560)). Qed.
Lemma lem3573685 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term871 _91307 _91560 x y) = (term872 _91307 _91560 x y).
Proof. exact (MK_COMB (@lem3573683 _91307 _91560 x y) (@lem3573684 _91307 _91560)). Qed.
Lemma lem3573686 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term873 _91307 _91560 x) = (term874 _91307 _91560 x).
Proof. exact (fun_ext (fun y : type628 _91307 _91560 => @lem3573685 _91307 _91560 x y)). Qed.
Lemma lem3573687 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573688 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term862 _91307 _91560 x) = (term875 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573687 _91307 _91560) (@lem3573686 _91307 _91560 x)). Qed.
Lemma lem3573689 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : ((term861 _91307 _91560 x) = (term862 _91307 _91560 x)) = ((term855 _91307 _91560 x) = (term875 _91307 _91560 x)).
Proof. exact (MK_COMB (@lem3573680 _91307 _91560 x) (@lem3573688 _91307 _91560 x)). Qed.
Lemma lem3573690 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term855 _91307 _91560 x) = (term875 _91307 _91560 x).
Proof. exact (EQ_MP (@lem3573689 _91307 _91560 x) (@lem3573670 _91307 _91560 x)). Qed.
Lemma lem3573692 {A : Type'} (P : Prop) (Q : A -> Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3573693 {_91307 _91560 : Type'} (P : Prop) (Q : type135 _91307 _91560) : (term876 _91307 _91560 P Q) = (term877 _91307 _91560 P Q).
Proof. exact (@lem3573692 (type630 _91307 _91560) P Q). Qed.
Lemma lem3573694 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term878 _91307 _91560 x y) = (term879 _91307 _91560 x y).
Proof. exact (@lem3573693 _91307 _91560 (term656 _91307 _91560 x y) (term839 _91307 _91560)). Qed.
Lemma lem3573695 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term880 _91307 _91560 y) = (term838 _91307 _91560 y).
Proof. exact (eq_refl (term880 _91307 _91560 y)). Qed.
Lemma lem3573696 {_91307 _91560 : Type'} : (term881 _91307 _91560) = (term839 _91307 _91560).
Proof. exact (fun_ext (fun y : type630 _91307 _91560 => @lem3573695 _91307 _91560 y)). Qed.
Lemma lem3573697 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573698 {_91307 _91560 : Type'} : (term882 _91307 _91560) = (term840 _91307 _91560).
Proof. exact (MK_COMB (@lem3573697 _91307 _91560) (@lem3573696 _91307 _91560)). Qed.
Lemma lem3573699 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term870 _91307 _91560 x y) = (term870 _91307 _91560 x y).
Proof. exact (eq_refl (term870 _91307 _91560 x y)). Qed.
Lemma lem3573700 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term878 _91307 _91560 x y) = (term872 _91307 _91560 x y).
Proof. exact (MK_COMB (@lem3573699 _91307 _91560 x y) (@lem3573698 _91307 _91560)). Qed.
Lemma lem3573701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573702 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term883 _91307 _91560 x y) = (term884 _91307 _91560 x y).
Proof. exact (MK_COMB (@lem3573701) (@lem3573700 _91307 _91560 x y)). Qed.
Lemma lem3573703 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term880 _91307 _91560 y) = (term838 _91307 _91560 y).
Proof. exact (eq_refl (term880 _91307 _91560 y)). Qed.
Lemma lem3573704 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term870 _91307 _91560 x y) = (term870 _91307 _91560 x y).
Proof. exact (eq_refl (term870 _91307 _91560 x y)). Qed.
Lemma lem3573705 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) : (term885 _91307 _91560 x y y') = (term886 _91307 _91560 x y y').
Proof. exact (MK_COMB (@lem3573704 _91307 _91560 x y) (@lem3573703 _91307 _91560 y')). Qed.
Lemma lem3573706 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term887 _91307 _91560 x y) = (term888 _91307 _91560 x y).
Proof. exact (fun_ext (fun y' : type630 _91307 _91560 => @lem3573705 _91307 _91560 x y y')). Qed.
Lemma lem3573707 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573708 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term879 _91307 _91560 x y) = (term889 _91307 _91560 x y).
Proof. exact (MK_COMB (@lem3573707 _91307 _91560) (@lem3573706 _91307 _91560 x y)). Qed.
Lemma lem3573709 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : ((term878 _91307 _91560 x y) = (term879 _91307 _91560 x y)) = ((term872 _91307 _91560 x y) = (term889 _91307 _91560 x y)).
Proof. exact (MK_COMB (@lem3573702 _91307 _91560 x y) (@lem3573708 _91307 _91560 x y)). Qed.
Lemma lem3573710 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term872 _91307 _91560 x y) = (term889 _91307 _91560 x y).
Proof. exact (EQ_MP (@lem3573709 _91307 _91560 x y) (@lem3573694 _91307 _91560 x y)). Qed.
Lemma lem3573712 {A : Type'} (P : Prop) (Q : A -> Prop) : (term157 A P Q) = (term158 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3573713 {_91307 _91560 : Type'} (P : Prop) (Q : type134 _91307 _91560) : (term890 _91307 _91560 P Q) = (term891 _91307 _91560 P Q).
Proof. exact (@lem3573712 (type629 _91307 _91560) P Q). Qed.
Lemma lem3573714 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) : (term892 _91307 _91560 x y y') = (term893 _91307 _91560 x y y').
Proof. exact (@lem3573713 _91307 _91560 (term656 _91307 _91560 x y) (term837 _91307 _91560 y')). Qed.
Lemma lem3573715 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (g : type629 _91307 _91560) : (term894 _91307 _91560 y g) = (term835 _91307 _91560 y g).
Proof. exact (eq_refl (term894 _91307 _91560 y g)). Qed.
Lemma lem3573716 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term895 _91307 _91560 y) = (term837 _91307 _91560 y).
Proof. exact (fun_ext (fun g : type629 _91307 _91560 => @lem3573715 _91307 _91560 y g)). Qed.
Lemma lem3573717 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573718 {_91307 _91560 : Type'} (y : type630 _91307 _91560) : (term896 _91307 _91560 y) = (term838 _91307 _91560 y).
Proof. exact (MK_COMB (@lem3573717 _91307 _91560) (@lem3573716 _91307 _91560 y)). Qed.
Lemma lem3573719 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term870 _91307 _91560 x y) = (term870 _91307 _91560 x y).
Proof. exact (eq_refl (term870 _91307 _91560 x y)). Qed.
Lemma lem3573720 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) : (term892 _91307 _91560 x y y') = (term886 _91307 _91560 x y y').
Proof. exact (MK_COMB (@lem3573719 _91307 _91560 x y) (@lem3573718 _91307 _91560 y')). Qed.
Lemma lem3573721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3573722 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) : (term897 _91307 _91560 x y y') = (term898 _91307 _91560 x y y').
Proof. exact (MK_COMB (@lem3573721) (@lem3573720 _91307 _91560 x y y')). Qed.
Lemma lem3573723 {_91307 _91560 : Type'} (y : type630 _91307 _91560) (g : type629 _91307 _91560) : (term894 _91307 _91560 y g) = (term835 _91307 _91560 y g).
Proof. exact (eq_refl (term894 _91307 _91560 y g)). Qed.
Lemma lem3573724 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term870 _91307 _91560 x y) = (term870 _91307 _91560 x y).
Proof. exact (eq_refl (term870 _91307 _91560 x y)). Qed.
Lemma lem3573725 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) (g : type629 _91307 _91560) : (term899 _91307 _91560 x y y' g) = (term900 _91307 _91560 x y y' g).
Proof. exact (MK_COMB (@lem3573724 _91307 _91560 x y) (@lem3573723 _91307 _91560 y' g)). Qed.
Lemma lem3573726 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) : (term901 _91307 _91560 x y y') = (term902 _91307 _91560 x y y').
Proof. exact (fun_ext (fun g : type629 _91307 _91560 => @lem3573725 _91307 _91560 x y y' g)). Qed.
Lemma lem3573727 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573728 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) : (term893 _91307 _91560 x y y') = (term903 _91307 _91560 x y y').
Proof. exact (MK_COMB (@lem3573727 _91307 _91560) (@lem3573726 _91307 _91560 x y y')). Qed.
Lemma lem3573729 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) : ((term892 _91307 _91560 x y y') = (term893 _91307 _91560 x y y')) = ((term886 _91307 _91560 x y y') = (term903 _91307 _91560 x y y')).
Proof. exact (MK_COMB (@lem3573722 _91307 _91560 x y y') (@lem3573728 _91307 _91560 x y y')). Qed.
Lemma lem3573730 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) : (term886 _91307 _91560 x y y') = (term903 _91307 _91560 x y y').
Proof. exact (EQ_MP (@lem3573729 _91307 _91560 x y y') (@lem3573714 _91307 _91560 x y y')). Qed.
Lemma lem3573731 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term888 _91307 _91560 x y) = (term904 _91307 _91560 x y).
Proof. exact (fun_ext (fun y' : type630 _91307 _91560 => @lem3573730 _91307 _91560 x y y')). Qed.
Lemma lem3573732 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560))). Qed.
Lemma lem3573733 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term889 _91307 _91560 x y) = (term905 _91307 _91560 x y).
Proof. exact (MK_COMB (@lem3573732 _91307 _91560) (@lem3573731 _91307 _91560 x y)). Qed.
Lemma lem3573734 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) : (term872 _91307 _91560 x y) = (term905 _91307 _91560 x y).
Proof. exact (TRANS (@lem3573710 _91307 _91560 x y) (@lem3573733 _91307 _91560 x y)). Qed.
Lemma lem3573735 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term874 _91307 _91560 x) = (term906 _91307 _91560 x).
Proof. exact (fun_ext (fun y : type628 _91307 _91560 => @lem3573734 _91307 _91560 x y)). Qed.
Lemma lem3573736 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> (_91560 -> _91307) -> _91560))). Qed.
Lemma lem3573737 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term875 _91307 _91560 x) = (term907 _91307 _91560 x).
Proof. exact (MK_COMB (@lem3573736 _91307 _91560) (@lem3573735 _91307 _91560 x)). Qed.
Lemma lem3573738 {_91307 _91560 : Type'} (x : type629 _91307 _91560) : (term855 _91307 _91560 x) = (term907 _91307 _91560 x).
Proof. exact (TRANS (@lem3573690 _91307 _91560 x) (@lem3573737 _91307 _91560 x)). Qed.
Lemma lem3573739 {_91307 _91560 : Type'} : (term857 _91307 _91560) = (term908 _91307 _91560).
Proof. exact (fun_ext (fun x : type629 _91307 _91560 => @lem3573738 _91307 _91560 x)). Qed.
Lemma lem3573740 {_91307 _91560 : Type'} : (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)) = (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307)).
Proof. exact (eq_refl (@ex ((_91307 -> Prop) -> (_91307 -> _91560) -> (_91560 -> Prop) -> _91560 -> _91307))). Qed.
Lemma lem3573741 {_91307 _91560 : Type'} : (term858 _91307 _91560) = (term909 _91307 _91560).
Proof. exact (MK_COMB (@lem3573740 _91307 _91560) (@lem3573739 _91307 _91560)). Qed.
Lemma lem3573742 {_91307 _91560 : Type'} : (term841 _91307 _91560) = (term909 _91307 _91560).
Proof. exact (TRANS (@lem3573666 _91307 _91560) (@lem3573741 _91307 _91560)). Qed.
Lemma lem3573743 {_91307 _91560 : Type'} : (term415 _91307 _91560) = (term909 _91307 _91560).
Proof. exact (TRANS (@lem3573642 _91307 _91560) (@lem3573742 _91307 _91560)). Qed.
Lemma lem3573744 {_91307 _91560 : Type'} : (term345 _91307 _91560) = (term909 _91307 _91560).
Proof. exact (TRANS (@lem3573043 _91307 _91560) (@lem3573743 _91307 _91560)). Qed.
Lemma lem3573745 {_91307 _91560 : Type'} : (term0 _91307 _91560) = (term909 _91307 _91560).
Proof. exact (TRANS (@lem3571746 _91307 _91560) (@lem3573744 _91307 _91560)). Qed.
Lemma lem3573746 {_91307 _91560 : Type'} (h1 : term0 _91307 _91560) : term909 _91307 _91560.
Proof. exact (EQ_MP (@lem3573745 _91307 _91560) (@lem3571229 _91307 _91560 h1)). Qed.
Lemma lem3573747 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (h1 : term907 _91307 _91560 x) : term907 _91307 _91560 x.
Proof. exact (h1). Qed.
Lemma lem3573748 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (h1 : term905 _91307 _91560 x y) : term905 _91307 _91560 x y.
Proof. exact (h1). Qed.
Lemma lem3573749 {_91307 _91560 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) (h1 : term903 _91307 _91560 x y y') : term903 _91307 _91560 x y y'.
Proof. exact (h1). Qed.
Lemma lem3573751 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (h1 : term272 _91560 _91563 x' f) : term272 _91560 _91563 x' f.
Proof. exact (h1). Qed.
Lemma lem3573752 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y'' : type569 _91560 _91563) (f : _91563 -> _91560) (h1 : term270 _91560 _91563 x' y'' f) : term270 _91560 _91563 x' y'' f.
Proof. exact (h1). Qed.
Lemma lem3573753 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y'' : type569 _91560 _91563) (y''' : _91560) (f : _91563 -> _91560) (h1 : term268 _91560 _91563 x' y'' y''' f) : term268 _91560 _91563 x' y'' y''' f.
Proof. exact (h1). Qed.
Lemma lem3573754 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y'' : type569 _91560 _91563) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term265 _91560 _91563 x' y'' y''' f g') : term265 _91560 _91563 x' y'' y''' f g'.
Proof. exact (h1). Qed.
Lemma lem3574392 {_91560 : Type'} : (@eq _91560) = (@eq _91560).
Proof. exact (eq_refl (@eq _91560)). Qed.
Lemma lem3574393 {_91560 _91563 : Type'} (f : _91563 -> _91560) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3574398 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574399 {_91560 _91563 : Type'} (f : _91560 -> _91563) (x : _91560) : (f x) = (@I (_91560 -> _91563) f x).
Proof. exact (@lem3574398 _91560 _91563 f x). Qed.
Lemma lem3574401 {_91560 _91563 : Type'} (g' : _91560 -> _91563) (y : _91560) : (g' y) = (@I (_91560 -> _91563) g' y).
Proof. exact (@lem3574399 _91560 _91563 g' y). Qed.
Lemma lem3574402 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) (y : _91560) : (term43 _91560 _91563 f g' y) = (term910 _91560 _91563 f g' y).
Proof. exact (MK_COMB (@lem3574393 _91560 _91563 f) (@lem3574401 _91560 _91563 g' y)). Qed.
Lemma lem3574404 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574405 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) : (f x) = (@I (_91563 -> _91560) f x).
Proof. exact (@lem3574404 _91563 _91560 f x). Qed.
Lemma lem3574406 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) (y : _91560) : (term910 _91560 _91563 f g' y) = (term911 _91560 _91563 f g' y).
Proof. exact (@lem3574405 _91560 _91563 f (@I (_91560 -> _91563) g' y)). Qed.
Lemma lem3574407 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) (y : _91560) : (term43 _91560 _91563 f g' y) = (term911 _91560 _91563 f g' y).
Proof. exact (TRANS (@lem3574402 _91560 _91563 f g' y) (@lem3574406 _91560 _91563 f g' y)). Qed.
Lemma lem3574408 {_91560 : Type'} (y : _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3574409 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) (y : _91560) : (term912 _91560 _91563 f g' y) = (term913 _91560 _91563 f g' y).
Proof. exact (MK_COMB (@lem3574392 _91560) (@lem3574407 _91560 _91563 f g' y)). Qed.
Lemma lem3574410 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) (y : _91560) : ((term43 _91560 _91563 f g' y) = y) = ((term911 _91560 _91563 f g' y) = y).
Proof. exact (MK_COMB (@lem3574409 _91560 _91563 f g' y) (@lem3574408 _91560 y)). Qed.
Lemma lem3574411 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) : (term44 _91560 _91563 f g') = (term914 _91560 _91563 f g').
Proof. exact (fun_ext (fun y : _91560 => @lem3574410 _91560 _91563 f g' y)). Qed.
Lemma lem3574412 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3574413 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) : (term45 _91560 _91563 f g') = (term915 _91560 _91563 f g').
Proof. exact (MK_COMB (@lem3574412 _91560) (@lem3574411 _91560 _91563 f g')). Qed.
Lemma lem3574414 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3574415 {_91560 : Type'} : (@eq _91560) = (@eq _91560).
Proof. exact (eq_refl (@eq _91560)). Qed.
Lemma lem3574420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574422 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) : (f x) = (@I (_91563 -> _91560) f x).
Proof. exact (@lem3574420 _91563 _91560 f x). Qed.
Lemma lem3574423 {_91560 : Type'} (y''' : _91560) : y''' = y'''.
Proof. exact (eq_refl y'''). Qed.
Lemma lem3574424 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) : (term916 _91560 _91563 f x) = (term917 _91560 _91563 f x).
Proof. exact (MK_COMB (@lem3574415 _91560) (@lem3574422 _91560 _91563 f x)). Qed.
Lemma lem3574425 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y''' : _91560) : ((f x) = y''') = ((@I (_91563 -> _91560) f x) = y''').
Proof. exact (MK_COMB (@lem3574424 _91560 _91563 f x) (@lem3574423 _91560 y''')). Qed.
Lemma lem3574426 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y''' : _91560) : (term57 _91560 _91563 f x y''') = (term918 _91560 _91563 f x y''').
Proof. exact (MK_COMB (@lem3574414) (@lem3574425 _91560 _91563 f x y''')). Qed.
Lemma lem3574427 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y''' : _91560) : (term59 _91560 _91563 f y''') = (term919 _91560 _91563 f y''').
Proof. exact (fun_ext (fun x : _91563 => @lem3574426 _91560 _91563 f x y''')). Qed.
Lemma lem3574428 {_91563 : Type'} : (@all _91563) = (@all _91563).
Proof. exact (eq_refl (@all _91563)). Qed.
Lemma lem3574429 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y''' : _91560) : (term60 _91560 _91563 f y''') = (term920 _91560 _91563 f y''').
Proof. exact (MK_COMB (@lem3574428 _91563) (@lem3574427 _91560 _91563 f y''')). Qed.
Lemma lem3574430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3574431 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y''' : _91560) : (term185 _91560 _91563 f y''') = (term921 _91560 _91563 f y''').
Proof. exact (MK_COMB (@lem3574430) (@lem3574429 _91560 _91563 f y''')). Qed.
Lemma lem3574432 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) : (term198 _91560 _91563 y''' f g') = (term922 _91560 _91563 y''' f g').
Proof. exact (MK_COMB (@lem3574431 _91560 _91563 f y''') (@lem3574413 _91560 _91563 f g')). Qed.
Lemma lem3574433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3574434 {_91560 : Type'} : (@eq _91560) = (@eq _91560).
Proof. exact (eq_refl (@eq _91560)). Qed.
Lemma lem3574435 {_91560 _91563 : Type'} (f : _91563 -> _91560) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3574436 {_91560 _91563 : Type'} (g : _91560 -> _91563) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3574441 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574442 {_91560 _91563 : Type'} (f : type569 _91560 _91563) (x : _91560 -> _91563) : (f x) = (@I ((_91560 -> _91563) -> _91560) f x).
Proof. exact (@lem3574441 (_91560 -> _91563) _91560 f x). Qed.
Lemma lem3574444 {_91560 _91563 : Type'} (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (y'' g) = (@I ((_91560 -> _91563) -> _91560) y'' g).
Proof. exact (@lem3574442 _91560 _91563 y'' g). Qed.
Lemma lem3574445 {_91560 _91563 : Type'} (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term923 _91560 _91563 y'' g) = (term924 _91560 _91563 y'' g).
Proof. exact (MK_COMB (@lem3574436 _91560 _91563 g) (@lem3574444 _91560 _91563 y'' g)). Qed.
Lemma lem3574447 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574448 {_91560 _91563 : Type'} (f : _91560 -> _91563) (x : _91560) : (f x) = (@I (_91560 -> _91563) f x).
Proof. exact (@lem3574447 _91560 _91563 f x). Qed.
Lemma lem3574449 {_91560 _91563 : Type'} (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term924 _91560 _91563 y'' g) = (term925 _91560 _91563 y'' g).
Proof. exact (@lem3574448 _91560 _91563 g (@I ((_91560 -> _91563) -> _91560) y'' g)). Qed.
Lemma lem3574450 {_91560 _91563 : Type'} (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term923 _91560 _91563 y'' g) = (term925 _91560 _91563 y'' g).
Proof. exact (TRANS (@lem3574445 _91560 _91563 y'' g) (@lem3574449 _91560 _91563 y'' g)). Qed.
Lemma lem3574451 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term926 _91560 _91563 f y'' g) = (term927 _91560 _91563 f y'' g).
Proof. exact (MK_COMB (@lem3574435 _91560 _91563 f) (@lem3574450 _91560 _91563 y'' g)). Qed.
Lemma lem3574453 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574454 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) : (f x) = (@I (_91563 -> _91560) f x).
Proof. exact (@lem3574453 _91563 _91560 f x). Qed.
Lemma lem3574455 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term927 _91560 _91563 f y'' g) = (term928 _91560 _91563 f y'' g).
Proof. exact (@lem3574454 _91560 _91563 f (term925 _91560 _91563 y'' g)). Qed.
Lemma lem3574456 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term926 _91560 _91563 f y'' g) = (term928 _91560 _91563 f y'' g).
Proof. exact (TRANS (@lem3574451 _91560 _91563 f y'' g) (@lem3574455 _91560 _91563 f y'' g)). Qed.
Lemma lem3574461 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574462 {_91560 _91563 : Type'} (f : type569 _91560 _91563) (x : _91560 -> _91563) : (f x) = (@I ((_91560 -> _91563) -> _91560) f x).
Proof. exact (@lem3574461 (_91560 -> _91563) _91560 f x). Qed.
Lemma lem3574464 {_91560 _91563 : Type'} (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (y'' g) = (@I ((_91560 -> _91563) -> _91560) y'' g).
Proof. exact (@lem3574462 _91560 _91563 y'' g). Qed.
Lemma lem3574465 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term929 _91560 _91563 f y'' g) = (term930 _91560 _91563 f y'' g).
Proof. exact (MK_COMB (@lem3574434 _91560) (@lem3574456 _91560 _91563 f y'' g)). Qed.
Lemma lem3574466 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : ((term926 _91560 _91563 f y'' g) = (y'' g)) = ((term928 _91560 _91563 f y'' g) = (@I ((_91560 -> _91563) -> _91560) y'' g)).
Proof. exact (MK_COMB (@lem3574465 _91560 _91563 f y'' g) (@lem3574464 _91560 _91563 y'' g)). Qed.
Lemma lem3574467 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term130 _91560 _91563 f y'' g) = (term931 _91560 _91563 f y'' g).
Proof. exact (MK_COMB (@lem3574433) (@lem3574466 _91560 _91563 f y'' g)). Qed.
Lemma lem3574468 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) : (term132 _91560 _91563 f y'') = (term932 _91560 _91563 f y'').
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3574467 _91560 _91563 f y'' g)). Qed.
Lemma lem3574469 {_91560 _91563 : Type'} : (@all (_91560 -> _91563)) = (@all (_91560 -> _91563)).
Proof. exact (eq_refl (@all (_91560 -> _91563))). Qed.
Lemma lem3574470 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) : (term134 _91560 _91563 f y'') = (term933 _91560 _91563 f y'').
Proof. exact (MK_COMB (@lem3574469 _91560 _91563) (@lem3574468 _91560 _91563 f y'')). Qed.
Lemma lem3574471 {_91560 : Type'} : (@eq _91560) = (@eq _91560).
Proof. exact (eq_refl (@eq _91560)). Qed.
Lemma lem3574472 {_91560 _91563 : Type'} (f : _91563 -> _91560) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3574477 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574478 {_91560 _91563 : Type'} (f : _91560 -> _91563) (x : _91560) : (f x) = (@I (_91560 -> _91563) f x).
Proof. exact (@lem3574477 _91560 _91563 f x). Qed.
Lemma lem3574480 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y : _91560) : (x' y) = (@I (_91560 -> _91563) x' y).
Proof. exact (@lem3574478 _91560 _91563 x' y). Qed.
Lemma lem3574481 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) (y : _91560) : (term43 _91560 _91563 f x' y) = (term910 _91560 _91563 f x' y).
Proof. exact (MK_COMB (@lem3574472 _91560 _91563 f) (@lem3574480 _91560 _91563 x' y)). Qed.
Lemma lem3574483 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3574484 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) : (f x) = (@I (_91563 -> _91560) f x).
Proof. exact (@lem3574483 _91563 _91560 f x). Qed.
Lemma lem3574485 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) (y : _91560) : (term910 _91560 _91563 f x' y) = (term911 _91560 _91563 f x' y).
Proof. exact (@lem3574484 _91560 _91563 f (@I (_91560 -> _91563) x' y)). Qed.
Lemma lem3574486 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) (y : _91560) : (term43 _91560 _91563 f x' y) = (term911 _91560 _91563 f x' y).
Proof. exact (TRANS (@lem3574481 _91560 _91563 f x' y) (@lem3574485 _91560 _91563 f x' y)). Qed.
Lemma lem3574487 {_91560 : Type'} (y : _91560) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3574488 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) (y : _91560) : (term912 _91560 _91563 f x' y) = (term913 _91560 _91563 f x' y).
Proof. exact (MK_COMB (@lem3574471 _91560) (@lem3574486 _91560 _91563 f x' y)). Qed.
Lemma lem3574489 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) (y : _91560) : ((term43 _91560 _91563 f x' y) = y) = ((term911 _91560 _91563 f x' y) = y).
Proof. exact (MK_COMB (@lem3574488 _91560 _91563 f x' y) (@lem3574487 _91560 y)). Qed.
Lemma lem3574490 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) : (term44 _91560 _91563 f x') = (term914 _91560 _91563 f x').
Proof. exact (fun_ext (fun y : _91560 => @lem3574489 _91560 _91563 f x' y)). Qed.
Lemma lem3574491 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3574492 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) : (term45 _91560 _91563 f x') = (term915 _91560 _91563 f x').
Proof. exact (MK_COMB (@lem3574491 _91560) (@lem3574490 _91560 _91563 f x')). Qed.
Lemma lem3574493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3574494 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) : (term151 _91560 _91563 f x') = (term934 _91560 _91563 f x').
Proof. exact (MK_COMB (@lem3574493) (@lem3574492 _91560 _91563 f x')). Qed.
Lemma lem3574495 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) : (term169 _91560 _91563 x' f y'') = (term935 _91560 _91563 x' f y'').
Proof. exact (MK_COMB (@lem3574494 _91560 _91563 f x') (@lem3574470 _91560 _91563 f y'')). Qed.
Lemma lem3574496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3574497 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) : (term235 _91560 _91563 x' f y'') = (term936 _91560 _91563 x' f y'').
Proof. exact (MK_COMB (@lem3574496) (@lem3574495 _91560 _91563 x' f y'')). Qed.
Lemma lem3574498 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y'' : type569 _91560 _91563) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) : (term265 _91560 _91563 x' y'' y''' f g') = (term937 _91560 _91563 x' y'' y''' f g').
Proof. exact (MK_COMB (@lem3574497 _91560 _91563 x' f y'') (@lem3574432 _91560 _91563 y''' f g')). Qed.
Lemma lem3574499 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y'' : type569 _91560 _91563) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term265 _91560 _91563 x' y'' y''' f g') : term937 _91560 _91563 x' y'' y''' f g'.
Proof. exact (EQ_MP (@lem3574498 _91560 _91563 x' y'' y''' f g') (@lem3573754 _91560 _91563 x' y'' y''' f g' h1)). Qed.
Lemma lem3574502 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term935 _91560 _91563 x' f y''.
Proof. exact (h1). Qed.
Lemma lem3574503 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term922 _91560 _91563 y''' f g'.
Proof. exact (h1). Qed.
Lemma lem3574504 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term933 _91560 _91563 f y''.
Proof. exact (proj2 (@lem3574502 _91560 _91563 x' f y'' h1)). Qed.
Lemma lem3574505 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term915 _91560 _91563 f x'.
Proof. exact (proj1 (@lem3574502 _91560 _91563 x' f y'' h1)). Qed.
Lemma lem3574506 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term915 _91560 _91563 f g'.
Proof. exact (proj2 (@lem3574503 _91560 _91563 y''' f g' h1)). Qed.
Lemma lem3574507 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term920 _91560 _91563 f y'''.
Proof. exact (proj1 (@lem3574503 _91560 _91563 y''' f g' h1)). Qed.
Lemma lem3574798 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) (y : _91560) : ((term911 _91560 _91563 f x' y) = y) = ((term911 _91560 _91563 f x' y) = y).
Proof. exact (eq_refl ((term911 _91560 _91563 f x' y) = y)). Qed.
Lemma lem3574799 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) : (term914 _91560 _91563 f x') = (term914 _91560 _91563 f x').
Proof. exact (fun_ext (fun y : _91560 => @lem3574798 _91560 _91563 f x' y)). Qed.
Lemma lem3574800 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3574802 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) : (term915 _91560 _91563 f x') = (term915 _91560 _91563 f x').
Proof. exact (MK_COMB (@lem3574800 _91560) (@lem3574799 _91560 _91563 f x')). Qed.
Lemma lem3574803 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term915 _91560 _91563 f x'.
Proof. exact (EQ_MP (@lem3574802 _91560 _91563 f x') (@lem3574505 _91560 _91563 x' f y'' h1)). Qed.
Lemma lem3574805 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (g : _91560 -> _91563) : (term931 _91560 _91563 f y'' g) = (term931 _91560 _91563 f y'' g).
Proof. exact (eq_refl (term931 _91560 _91563 f y'' g)). Qed.
Lemma lem3574806 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) : (term932 _91560 _91563 f y'') = (term932 _91560 _91563 f y'').
Proof. exact (fun_ext (fun g : _91560 -> _91563 => @lem3574805 _91560 _91563 f y'' g)). Qed.
Lemma lem3574807 {_91560 _91563 : Type'} : (@all (_91560 -> _91563)) = (@all (_91560 -> _91563)).
Proof. exact (eq_refl (@all (_91560 -> _91563))). Qed.
Lemma lem3574809 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) : (term933 _91560 _91563 f y'') = (term933 _91560 _91563 f y'').
Proof. exact (MK_COMB (@lem3574807 _91560 _91563) (@lem3574806 _91560 _91563 f y'')). Qed.
Lemma lem3574810 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term933 _91560 _91563 f y''.
Proof. exact (EQ_MP (@lem3574809 _91560 _91563 f y'') (@lem3574504 _91560 _91563 x' f y'' h1)). Qed.
Lemma lem3575101 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x : _91563) (y''' : _91560) : (term918 _91560 _91563 f x y''') = (term918 _91560 _91563 f x y''').
Proof. exact (eq_refl (term918 _91560 _91563 f x y''')). Qed.
Lemma lem3575102 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y''' : _91560) : (term919 _91560 _91563 f y''') = (term919 _91560 _91563 f y''').
Proof. exact (fun_ext (fun x : _91563 => @lem3575101 _91560 _91563 f x y''')). Qed.
Lemma lem3575103 {_91563 : Type'} : (@all _91563) = (@all _91563).
Proof. exact (eq_refl (@all _91563)). Qed.
Lemma lem3575105 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y''' : _91560) : (term920 _91560 _91563 f y''') = (term920 _91560 _91563 f y''').
Proof. exact (MK_COMB (@lem3575103 _91563) (@lem3575102 _91560 _91563 f y''')). Qed.
Lemma lem3575106 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term920 _91560 _91563 f y'''.
Proof. exact (EQ_MP (@lem3575105 _91560 _91563 f y''') (@lem3574507 _91560 _91563 y''' f g' h1)). Qed.
Lemma lem3575108 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) (y : _91560) : ((term911 _91560 _91563 f g' y) = y) = ((term911 _91560 _91563 f g' y) = y).
Proof. exact (eq_refl ((term911 _91560 _91563 f g' y) = y)). Qed.
Lemma lem3575109 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) : (term914 _91560 _91563 f g') = (term914 _91560 _91563 f g').
Proof. exact (fun_ext (fun y : _91560 => @lem3575108 _91560 _91563 f g' y)). Qed.
Lemma lem3575110 {_91560 : Type'} : (@all _91560) = (@all _91560).
Proof. exact (eq_refl (@all _91560)). Qed.
Lemma lem3575112 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) : (term915 _91560 _91563 f g') = (term915 _91560 _91563 f g').
Proof. exact (MK_COMB (@lem3575110 _91560) (@lem3575109 _91560 _91563 f g')). Qed.
Lemma lem3575113 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term915 _91560 _91563 f g'.
Proof. exact (EQ_MP (@lem3575112 _91560 _91563 f g') (@lem3574506 _91560 _91563 y''' f g' h1)). Qed.
Lemma lem3575150 {_91560 _91563 : Type'} (_38431 : _91560) (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term938 _91560 _91563 f x' _38431.
Proof. exact (@lem3574803 _91560 _91563 x' f y'' h1 _38431). Qed.
Lemma lem3575151 {_91560 _91563 : Type'} (f : _91563 -> _91560) (x' : _91560 -> _91563) (_38431 : _91560) : (term938 _91560 _91563 f x' _38431) = ((term911 _91560 _91563 f x' _38431) = _38431).
Proof. exact (eq_refl (term938 _91560 _91563 f x' _38431)). Qed.
Lemma lem3575153 {_91560 _91563 : Type'} (_38432 : _91560 -> _91563) (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term939 _91560 _91563 f y'' _38432.
Proof. exact (@lem3574810 _91560 _91563 x' f y'' h1 _38432). Qed.
Lemma lem3575154 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (_38432 : _91560 -> _91563) : (term939 _91560 _91563 f y'' _38432) = (term931 _91560 _91563 f y'' _38432).
Proof. exact (eq_refl (term939 _91560 _91563 f y'' _38432)). Qed.
Lemma lem3575192 {_91560 _91563 : Type'} (_38445 : _91563) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term940 _91560 _91563 f y''' _38445.
Proof. exact (@lem3575106 _91560 _91563 y''' f g' h1 _38445). Qed.
Lemma lem3575193 {_91560 _91563 : Type'} (f : _91563 -> _91560) (_38445 : _91563) (y''' : _91560) : (term940 _91560 _91563 f y''' _38445) = (term918 _91560 _91563 f _38445 y''').
Proof. exact (eq_refl (term940 _91560 _91563 f y''' _38445)). Qed.
Lemma lem3575195 {_91560 _91563 : Type'} (_38446 : _91560) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term938 _91560 _91563 f g' _38446.
Proof. exact (@lem3575113 _91560 _91563 y''' f g' h1 _38446). Qed.
Lemma lem3575196 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) (_38446 : _91560) : (term938 _91560 _91563 f g' _38446) = ((term911 _91560 _91563 f g' _38446) = _38446).
Proof. exact (eq_refl (term938 _91560 _91563 f g' _38446)). Qed.
Lemma lem3575229 {_91560 _91563 : Type'} (_38432 : _91560 -> _91563) (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term931 _91560 _91563 f y'' _38432.
Proof. exact (EQ_MP (@lem3575154 _91560 _91563 f y'' _38432) (@lem3575153 _91560 _91563 _38432 x' f y'' h1)). Qed.
Lemma lem3575343 {_91560 _91563 : Type'} (_38445 : _91563) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term918 _91560 _91563 f _38445 y'''.
Proof. exact (EQ_MP (@lem3575193 _91560 _91563 f _38445 y''') (@lem3575192 _91560 _91563 _38445 y''' f g' h1)). Qed.
Lemma lem3575796 {_91560 _91563 : Type'} (_38431 : _91560) (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : (term911 _91560 _91563 f x' _38431) = _38431.
Proof. exact (EQ_MP (@lem3575151 _91560 _91563 f x' _38431) (@lem3575150 _91560 _91563 _38431 x' f y'' h1)). Qed.
Lemma lem3575797 {_91560 _91563 : Type'} (_38431 : _91560) (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : (term911 _91560 _91563 f x' _38431) = _38431.
Proof. exact (@lem3575796 _91560 _91563 _38431 x' f y'' h1). Qed.
Lemma lem3575798 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : (term928 _91560 _91563 f y'' x') = (@I ((_91560 -> _91563) -> _91560) y'' x').
Proof. exact (@lem3575797 _91560 _91563 (@I ((_91560 -> _91563) -> _91560) y'' x') x' f y'' h1). Qed.
Lemma lem3575799 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term941 _91560 _91563 f y'' x'.
Proof. exact (fun h0 : term931 _91560 _91563 f y'' x' => @lem3575798 _91560 _91563 x' f y'' h1). Qed.
Lemma lem3575801 (p : Prop) : (term942 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3575802 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (x' : _91560 -> _91563) : (term941 _91560 _91563 f y'' x') = ((term928 _91560 _91563 f y'' x') = (@I ((_91560 -> _91563) -> _91560) y'' x')).
Proof. exact (@lem3575801 ((term928 _91560 _91563 f y'' x') = (@I ((_91560 -> _91563) -> _91560) y'' x'))). Qed.
Lemma lem3575803 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : (term928 _91560 _91563 f y'' x') = (@I ((_91560 -> _91563) -> _91560) y'' x').
Proof. exact (EQ_MP (@lem3575802 _91560 _91563 f y'' x') (@lem3575799 _91560 _91563 x' f y'' h1)). Qed.
Lemma lem3575806 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3575808 {_91560 _91563 : Type'} (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (_38432 : _91560 -> _91563) : (term931 _91560 _91563 f y'' _38432) = (term943 _91560 _91563 f y'' _38432).
Proof. exact (@lem3575806 ((term928 _91560 _91563 f y'' _38432) = (@I ((_91560 -> _91563) -> _91560) y'' _38432))). Qed.
Lemma lem3575811 {_91560 _91563 : Type'} (_38432 : _91560 -> _91563) (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term943 _91560 _91563 f y'' _38432.
Proof. exact (EQ_MP (@lem3575808 _91560 _91563 f y'' _38432) (@lem3575229 _91560 _91563 _38432 x' f y'' h1)). Qed.
Lemma lem3575812 {_91560 _91563 : Type'} (_38432 : _91560 -> _91563) (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term943 _91560 _91563 f y'' _38432.
Proof. exact (@lem3575811 _91560 _91563 _38432 x' f y'' h1). Qed.
Lemma lem3575813 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term943 _91560 _91563 f y'' x'.
Proof. exact (@lem3575812 _91560 _91563 x' x' f y'' h1). Qed.
Lemma lem3575816 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : False.
Proof. exact (@lem3575813 _91560 _91563 x' f y'' h1 (@lem3575803 _91560 _91563 x' f y'' h1)). Qed.
Lemma lem3575817 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : term944.
Proof. exact (fun h0 : ~ False => @lem3575816 _91560 _91563 x' f y'' h1). Qed.
Lemma lem3575819 (p : Prop) : (term942 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3575820 : term944 = False.
Proof. exact (@lem3575819 False). Qed.
Lemma lem3575821 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (y'' : type569 _91560 _91563) (h1 : term935 _91560 _91563 x' f y'') : False.
Proof. exact (EQ_MP (@lem3575820) (@lem3575817 _91560 _91563 x' f y'' h1)). Qed.
Lemma lem3576147 {_91560 _91563 : Type'} (_38446 : _91560) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : (term911 _91560 _91563 f g' _38446) = _38446.
Proof. exact (EQ_MP (@lem3575196 _91560 _91563 f g' _38446) (@lem3575195 _91560 _91563 _38446 y''' f g' h1)). Qed.
Lemma lem3576148 {_91560 _91563 : Type'} (_38446 : _91560) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : (term911 _91560 _91563 f g' _38446) = _38446.
Proof. exact (@lem3576147 _91560 _91563 _38446 y''' f g' h1). Qed.
Lemma lem3576149 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : (term911 _91560 _91563 f g' y''') = y'''.
Proof. exact (@lem3576148 _91560 _91563 y''' y''' f g' h1). Qed.
Lemma lem3576150 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term945 _91560 _91563 f g' y'''.
Proof. exact (fun h0 : term946 _91560 _91563 f g' y''' => @lem3576149 _91560 _91563 y''' f g' h1). Qed.
Lemma lem3576152 (p : Prop) : (term942 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3576153 {_91560 _91563 : Type'} (f : _91563 -> _91560) (g' : _91560 -> _91563) (y''' : _91560) : (term945 _91560 _91563 f g' y''') = ((term911 _91560 _91563 f g' y''') = y''').
Proof. exact (@lem3576152 ((term911 _91560 _91563 f g' y''') = y''')). Qed.
Lemma lem3576154 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : (term911 _91560 _91563 f g' y''') = y'''.
Proof. exact (EQ_MP (@lem3576153 _91560 _91563 f g' y''') (@lem3576150 _91560 _91563 y''' f g' h1)). Qed.
Lemma lem3576157 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3576159 {_91560 _91563 : Type'} (f : _91563 -> _91560) (_38445 : _91563) (y''' : _91560) : (term918 _91560 _91563 f _38445 y''') = (term947 _91560 _91563 f _38445 y''').
Proof. exact (@lem3576157 ((@I (_91563 -> _91560) f _38445) = y''')). Qed.
Lemma lem3576162 {_91560 _91563 : Type'} (_38445 : _91563) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term947 _91560 _91563 f _38445 y'''.
Proof. exact (EQ_MP (@lem3576159 _91560 _91563 f _38445 y''') (@lem3575343 _91560 _91563 _38445 y''' f g' h1)). Qed.
Lemma lem3576163 {_91560 _91563 : Type'} (_38445 : _91563) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term947 _91560 _91563 f _38445 y'''.
Proof. exact (@lem3576162 _91560 _91563 _38445 y''' f g' h1). Qed.
Lemma lem3576164 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term948 _91560 _91563 f g' y'''.
Proof. exact (@lem3576163 _91560 _91563 (@I (_91560 -> _91563) g' y''') y''' f g' h1). Qed.
Lemma lem3576167 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : False.
Proof. exact (@lem3576164 _91560 _91563 y''' f g' h1 (@lem3576154 _91560 _91563 y''' f g' h1)). Qed.
Lemma lem3576168 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : term944.
Proof. exact (fun h0 : ~ False => @lem3576167 _91560 _91563 y''' f g' h1). Qed.
Lemma lem3576170 (p : Prop) : (term942 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3576171 : term944 = False.
Proof. exact (@lem3576170 False). Qed.
Lemma lem3576172 {_91560 _91563 : Type'} (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term922 _91560 _91563 y''' f g') : False.
Proof. exact (EQ_MP (@lem3576171) (@lem3576168 _91560 _91563 y''' f g' h1)). Qed.
Lemma lem3576173 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y'' : type569 _91560 _91563) (y''' : _91560) (f : _91563 -> _91560) (g' : _91560 -> _91563) (h1 : term265 _91560 _91563 x' y'' y''' f g') : False.
Proof. exact (or_elim (@lem3574499 _91560 _91563 x' y'' y''' f g' h1) (fun h0 : term935 _91560 _91563 x' f y'' => @lem3575821 _91560 _91563 x' f y'' h0) (fun h0 : term922 _91560 _91563 y''' f g' => @lem3576172 _91560 _91563 y''' f g' h0)). Qed.
Lemma lem3576174 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y'' : type569 _91560 _91563) (y''' : _91560) (f : _91563 -> _91560) (h1 : term268 _91560 _91563 x' y'' y''' f) : False.
Proof. exact (ex_elim (@lem3573753 _91560 _91563 x' y'' y''' f h1) (fun g' : _91560 -> _91563 => fun h0 : term267 _91560 _91563 x' y'' y''' f g' => @lem3576173 _91560 _91563 x' y'' y''' f g' h0)). Qed.
Lemma lem3576175 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (y'' : type569 _91560 _91563) (f : _91563 -> _91560) (h1 : term270 _91560 _91563 x' y'' f) : False.
Proof. exact (ex_elim (@lem3573752 _91560 _91563 x' y'' f h1) (fun y''' : _91560 => fun h0 : term269 _91560 _91563 x' y'' f y''' => @lem3576174 _91560 _91563 x' y'' y''' f h0)). Qed.
Lemma lem3576176 {_91560 _91563 : Type'} (x' : _91560 -> _91563) (f : _91563 -> _91560) (h1 : term272 _91560 _91563 x' f) : False.
Proof. exact (ex_elim (@lem3573751 _91560 _91563 x' f h1) (fun y'' : type569 _91560 _91563 => fun h0 : term271 _91560 _91563 x' f y'' => @lem3576175 _91560 _91563 x' y'' f h0)). Qed.
Lemma lem3576177 {_91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : False.
Proof. exact (ex_elim (@lem3571600 _91560 _91563 f h1) (fun x' : _91560 -> _91563 => fun h0 : term273 _91560 _91563 f x' => @lem3576176 _91560 _91563 x' f h0)). Qed.
Lemma lem3576178 {_91307 _91560 _91563 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (y' : type630 _91307 _91560) (f : _91563 -> _91560) (h1 : term903 _91307 _91560 x y y') (h2 : term5 _91560 _91563 f) : False.
Proof. exact (ex_elim (@lem3573749 _91307 _91560 x y y' h1) (fun g : type629 _91307 _91560 => fun h0 : term902 _91307 _91560 x y y' g => @lem3576177 _91560 _91563 f h2)). Qed.
Lemma lem3576179 {_91307 _91560 _91563 : Type'} (x : type629 _91307 _91560) (y : type628 _91307 _91560) (f : _91563 -> _91560) (h1 : term905 _91307 _91560 x y) (h2 : term5 _91560 _91563 f) : False.
Proof. exact (ex_elim (@lem3573748 _91307 _91560 x y h1) (fun y' : type630 _91307 _91560 => fun h0 : term904 _91307 _91560 x y y' => @lem3576178 _91307 _91560 _91563 x y y' f h0 h2)). Qed.
Lemma lem3576180 {_91307 _91560 _91563 : Type'} (x : type629 _91307 _91560) (f : _91563 -> _91560) (h1 : term907 _91307 _91560 x) (h2 : term5 _91560 _91563 f) : False.
Proof. exact (ex_elim (@lem3573747 _91307 _91560 x h1) (fun y : type628 _91307 _91560 => fun h0 : term906 _91307 _91560 x y => @lem3576179 _91307 _91560 _91563 x y f h0 h2)). Qed.
Lemma lem3576181 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term0 _91307 _91560) (h2 : term5 _91560 _91563 f) : False.
Proof. exact (ex_elim (@lem3573746 _91307 _91560 h1) (fun x : type629 _91307 _91560 => fun h0 : term908 _91307 _91560 x => @lem3576180 _91307 _91560 _91563 x f h0 h2)). Qed.
Lemma lem3576182 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term11 _91307 _91560.
Proof. exact (fun h0 : term0 _91307 _91560 => @lem3576181 _91307 _91560 _91563 f h0 h1). Qed.
Lemma lem3576183 {_91307 _91560 : Type'} : (term11 _91307 _91560) = (term12 _91307 _91560).
Proof. exact (@lem69 (term0 _91307 _91560)). Qed.
Lemma lem3576184 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term12 _91307 _91560.
Proof. exact (EQ_MP (@lem3576183 _91307 _91560) (@lem3576182 _91307 _91560 _91563 f h1)). Qed.
Lemma lem3576185 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term15 _91307 _91560.
Proof. exact (fun h0 : term6 _91560 => @lem3576184 _91307 _91560 _91563 f h1). Qed.
Lemma lem3576186 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term17 _91307 _91560.
Proof. exact (fun h0 : term6 _91307 => @lem3576185 _91307 _91560 _91563 f h1). Qed.
Lemma lem3576187 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : term19 _91307 _91560 _91563 f.
Proof. exact (fun h0 : term5 _91560 _91563 f => @lem3576186 _91307 _91560 _91563 f h0). Qed.
Lemma lem3576192 {_91307 _91560 _91563 : Type'} : term23 _91307 _91560 _91563.
Proof. exact (fun f : _91563 -> _91560 => @lem3576187 _91307 _91560 _91563 f). Qed.
Lemma lem3576193 {_91307 _91560 _91563 : Type'} : term22 _91307 _91560 _91563.
Proof. exact (EQ_MP (@lem3571225 _91307 _91560 _91563) (@lem3576192 _91307 _91560 _91563)). Qed.
Lemma lem3576194 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : term949 _91307 _91560 _91563 f.
Proof. exact (@lem3576193 _91307 _91560 _91563 f). Qed.
Lemma lem3576195 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : (term949 _91307 _91560 _91563 f) = (term7 _91307 _91560 _91563 f).
Proof. exact (eq_refl (term949 _91307 _91560 _91563 f)). Qed.
Lemma lem3576196 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : term7 _91307 _91560 _91563 f.
Proof. exact (EQ_MP (@lem3576195 _91307 _91560 _91563 f) (@lem3576194 _91307 _91560 _91563 f)). Qed.
Lemma lem3576198 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) : term7 _91307 _91560 _91563 f.
Proof. exact (@lem3570900 _91307 _91560 _91563 f (@lem3576196 _91307 _91560 _91563 f)). Qed.
Lemma lem3576199 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term16 _91307 _91560.
Proof. exact (@lem3576198 _91307 _91560 _91563 f (@lem3570881 _91560 _91563 f h1)). Qed.
Lemma lem3576200 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term14 _91307 _91560.
Proof. exact (@lem3576199 _91307 _91560 _91563 f h1 (@lem3570884 _91307)). Qed.
Lemma lem3576201 {_91307 _91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : term11 _91307 _91560.
Proof. exact (@lem3576200 _91307 _91560 _91563 f h1 (@lem3570883 _91560)). Qed.
Lemma lem3576202 {_91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : False.
Proof. exact (@lem3576201 Prop _91560 _91563 f h1 (@lem3570882 Prop _91560)). Qed.
Lemma lem3576203 {_91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : (term5 _91560 _91563 f) = False.
Proof. exact (prop_ext (fun h2 : term5 _91560 _91563 f => @lem3576202 _91560 _91563 f h1) (fun h2 : False => @lem3570881 _91560 _91563 f h1)). Qed.
Lemma lem3576204 {_91560 _91563 : Type'} (f : _91563 -> _91560) (h1 : term5 _91560 _91563 f) : False.
Proof. exact (EQ_MP (@lem3576203 _91560 _91563 f h1) (@lem3570881 _91560 _91563 f h1)). Qed.
Lemma lem3576205 {_91560 _91563 : Type'} (f : _91563 -> _91560) : term4 _91560 _91563 f.
Proof. exact (fun h0 : term5 _91560 _91563 f => @lem3576204 _91560 _91563 f h0). Qed.
Lemma lem3576206 {_91560 _91563 : Type'} (f : _91563 -> _91560) : (term2 _91560 _91563 f) = (term3 _91560 _91563 f).
Proof. exact (EQ_MP (@lem3570880 _91560 _91563 f) (@lem3576205 _91560 _91563 f)). Qed.
