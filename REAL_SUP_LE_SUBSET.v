Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_LE_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_SUP_LE_spec.
Require Import SUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem5160983 (t : real -> Prop) : term0 t.
Proof. exact (@lem5136700 t). Qed.
Lemma lem5160984 (t : real -> Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem5160985 (t : real -> Prop) : term1 t.
Proof. exact (EQ_MP (@lem5160984 t) (@lem5160983 t)). Qed.
Lemma lem5160986 (s : real -> Prop) (h1 : term2 s) : term2 s.
Proof. exact (h1). Qed.
Lemma lem5160987 (b : real) (s : real -> Prop) (h1 : term2 s) : term3 s b.
Proof. exact (@lem5160986 s h1 b). Qed.
Lemma lem5160988 (s : real -> Prop) (b : real) : (term3 s b) = (term4 s b).
Proof. exact (eq_refl (term3 s b)). Qed.
Lemma lem5160989 (b : real) (s : real -> Prop) (h1 : term2 s) : term4 s b.
Proof. exact (EQ_MP (@lem5160988 s b) (@lem5160987 b s h1)). Qed.
Lemma lem5160990 (s : real -> Prop) (b : real) (h1 : term5 s b) : term5 s b.
Proof. exact (h1). Qed.
Lemma lem5160991 (s : real -> Prop) (b : real) (h1 : term2 s) (h2 : term5 s b) : term6 s b.
Proof. exact (@lem5160989 b s h1 (@lem5160990 s b h2)). Qed.
Lemma lem5160992 (s : real -> Prop) (b : real) (h1 : term5 s b) : term7 s b.
Proof. exact (fun h0 : term2 s => @lem5160991 s b h0 h1). Qed.
Lemma lem5160993 (s : real -> Prop) (h1 : term2 s) : term2 s.
Proof. exact (h1). Qed.
Lemma lem5160994 (s : real -> Prop) (b : real) (h1 : term2 s) (h2 : term5 s b) : term6 s b.
Proof. exact (@lem5160992 s b h2 (@lem5160993 s h1)). Qed.
Lemma lem5160995 (b : real) (s : real -> Prop) (h1 : term2 s) : term4 s b.
Proof. exact (fun h0 : term5 s b => @lem5160994 s b h1 h0). Qed.
Lemma lem5160996 (s : real -> Prop) (h1 : term2 s) : term2 s.
Proof. exact (fun b : real => @lem5160995 b s h1). Qed.
Lemma lem5160997 (s : real -> Prop) : term8 s.
Proof. exact (fun h0 : term2 s => @lem5160996 s h0). Qed.
Lemma lem5160998 (s : real -> Prop) : term2 s.
Proof. exact (@lem5160997 s (@lem5160982 s)). Qed.
Lemma lem5160999 (s : real -> Prop) (b : real) : term3 s b.
Proof. exact (@lem5160998 s b). Qed.
Lemma lem5161000 (s : real -> Prop) (b : real) : (term3 s b) = (term4 s b).
Proof. exact (eq_refl (term3 s b)). Qed.
Lemma lem5161002 (s : real -> Prop) (t : real -> Prop) (h1 : term9 s t) : term9 s t.
Proof. exact (h1). Qed.
Lemma lem5161003 (s : real -> Prop) (t : real -> Prop) (h1 : term10 s t) : term10 s t.
Proof. exact (h1). Qed.
Lemma lem5161004 (s : real -> Prop) (h1 : term11 s) : term11 s.
Proof. exact (h1). Qed.
Lemma lem5161005 (t : real -> Prop) (h1 : term12 t) : term12 t.
Proof. exact (h1). Qed.
Lemma lem5161006 (s : real -> Prop) (t : real -> Prop) (h1 : @SUBSET real s t) : @SUBSET real s t.
Proof. exact (h1). Qed.
Lemma lem5161007 (t : real -> Prop) (b : real) (h1 : term13 t b) : term13 t b.
Proof. exact (h1). Qed.
Lemma lem5161009 (s : real -> Prop) (b : real) : term4 s b.
Proof. exact (EQ_MP (@lem5161000 s b) (@lem5160999 s b)). Qed.
Lemma lem5161010 (s : real -> Prop) (t : real -> Prop) : term14 s t.
Proof. exact (@lem5161009 s (sup t)). Qed.
Lemma lem5161021 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : @SUBSET real s t) : term15 t s.
Proof. exact (conj (@lem5161006 s t h2) (@lem5161004 s h1)). Qed.
Lemma lem5161022 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 t b) (h2 : term11 s) (h3 : @SUBSET real s t) : term16 b t s.
Proof. exact (conj (@lem5161007 t b h1) (@lem5161021 s t h2 h3)). Qed.
Lemma lem5161036 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5161037 (s : real -> Prop) (t : real -> Prop) : (@SUBSET real s t) = (term18 s t).
Proof. exact (@lem5161036 real s t). Qed.
Lemma lem5161044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161045 (s : real -> Prop) (t : real -> Prop) : (term19 s t) = (term20 s t).
Proof. exact (MK_COMB (@lem5161044) (@lem5161037 s t)). Qed.
Lemma lem5161049 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5161050 (s : real -> Prop) (t : real -> Prop) : (s = t) = (term22 s t).
Proof. exact (@lem5161049 real s t). Qed.
Lemma lem5161051 (s : real -> Prop) : (s = (@EMPTY real)) = (term23 s).
Proof. exact (@lem5161050 s (@EMPTY real)). Qed.
Lemma lem5161060 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161061 (s : real -> Prop) : (term11 s) = (term24 s).
Proof. exact (MK_COMB (@lem5161060) (@lem5161051 s)). Qed.
Lemma lem5161062 (t : real -> Prop) (s : real -> Prop) : (term15 t s) = (term25 t s).
Proof. exact (MK_COMB (@lem5161045 s t) (@lem5161061 s)). Qed.
Lemma lem5161065 (t : real -> Prop) (b : real) : (term26 t b) = (term26 t b).
Proof. exact (eq_refl (term26 t b)). Qed.
Lemma lem5161066 (b : real) (t : real -> Prop) (s : real -> Prop) : (term16 b t s) = (term27 b t s).
Proof. exact (MK_COMB (@lem5161065 t b) (@lem5161062 t s)). Qed.
Lemma lem5161069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161070 (b : real) (t : real -> Prop) (s : real -> Prop) : (term28 b t s) = (term29 b t s).
Proof. exact (MK_COMB (@lem5161069) (@lem5161066 b t s)). Qed.
Lemma lem5161080 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5161081 (s : real -> Prop) (t : real -> Prop) : (s = t) = (term22 s t).
Proof. exact (@lem5161080 real s t). Qed.
Lemma lem5161082 (t : real -> Prop) : (t = (@EMPTY real)) = (term23 t).
Proof. exact (@lem5161081 t (@EMPTY real)). Qed.
Lemma lem5161091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161092 (t : real -> Prop) : (term11 t) = (term24 t).
Proof. exact (MK_COMB (@lem5161091) (@lem5161082 t)). Qed.
Lemma lem5161093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161094 (t : real -> Prop) : (term30 t) = (term31 t).
Proof. exact (MK_COMB (@lem5161093) (@lem5161092 t)). Qed.
Lemma lem5161105 (t : real -> Prop) : (term12 t) = (term12 t).
Proof. exact (eq_refl (term12 t)). Qed.
Lemma lem5161106 (t : real -> Prop) : (term32 t) = (term33 t).
Proof. exact (MK_COMB (@lem5161094 t) (@lem5161105 t)). Qed.
Lemma lem5161109 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161110 (t : real -> Prop) : (term34 t) = (term35 t).
Proof. exact (MK_COMB (@lem5161109) (@lem5161106 t)). Qed.
Lemma lem5161131 (t : real -> Prop) : (term36 t) = (term36 t).
Proof. exact (eq_refl (term36 t)). Qed.
Lemma lem5161132 (t : real -> Prop) : (term1 t) = (term37 t).
Proof. exact (MK_COMB (@lem5161110 t) (@lem5161131 t)). Qed.
Lemma lem5161135 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161136 (t : real -> Prop) : (term38 t) = (term39 t).
Proof. exact (MK_COMB (@lem5161135) (@lem5161132 t)). Qed.
Lemma lem5161142 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5161143 (s : real -> Prop) (t : real -> Prop) : (s = t) = (term22 s t).
Proof. exact (@lem5161142 real s t). Qed.
Lemma lem5161144 (s : real -> Prop) : (s = (@EMPTY real)) = (term23 s).
Proof. exact (@lem5161143 s (@EMPTY real)). Qed.
Lemma lem5161153 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161154 (s : real -> Prop) : (term11 s) = (term24 s).
Proof. exact (MK_COMB (@lem5161153) (@lem5161144 s)). Qed.
Lemma lem5161155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161156 (s : real -> Prop) : (term30 s) = (term31 s).
Proof. exact (MK_COMB (@lem5161155) (@lem5161154 s)). Qed.
Lemma lem5161163 (s : real -> Prop) (t : real -> Prop) : (term40 s t) = (term40 s t).
Proof. exact (eq_refl (term40 s t)). Qed.
Lemma lem5161164 (s : real -> Prop) (t : real -> Prop) : (term41 s t) = (term42 s t).
Proof. exact (MK_COMB (@lem5161156 s) (@lem5161163 s t)). Qed.
Lemma lem5161167 (s : real -> Prop) (t : real -> Prop) : (term43 s t) = (term44 s t).
Proof. exact (MK_COMB (@lem5161136 t) (@lem5161164 s t)). Qed.
Lemma lem5161170 (b : real) (s : real -> Prop) (t : real -> Prop) : (term45 b s t) = (term46 b s t).
Proof. exact (MK_COMB (@lem5161070 b t s) (@lem5161167 s t)). Qed.
Lemma lem5161173 (b : real) (s : real -> Prop) (t : real -> Prop) : (term46 b s t) = (term45 b s t).
Proof. exact (SYM (@lem5161170 b s t)). Qed.
Lemma lem5161185 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161186 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161185 real P x). Qed.
Lemma lem5161187 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5161186 t x). Qed.
Lemma lem5161188 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161189 (t : real -> Prop) (x : real) : (term47 x t) = (term48 t x).
Proof. exact (MK_COMB (@lem5161188) (@lem5161187 t x)). Qed.
Lemma lem5161190 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5161191 (t : real -> Prop) (x : real) (b : real) : (term49 t x b) = (term50 t x b).
Proof. exact (MK_COMB (@lem5161189 t x) (@lem5161190 x b)). Qed.
Lemma lem5161194 (t : real -> Prop) (b : real) : (term51 t b) = (term52 t b).
Proof. exact (fun_ext (fun x : real => @lem5161191 t x b)). Qed.
Lemma lem5161195 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161196 (t : real -> Prop) (b : real) : (term13 t b) = (term53 t b).
Proof. exact (MK_COMB (@lem5161195) (@lem5161194 t b)). Qed.
Lemma lem5161201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161202 (t : real -> Prop) (b : real) : (term26 t b) = (term54 t b).
Proof. exact (MK_COMB (@lem5161201) (@lem5161196 t b)). Qed.
Lemma lem5161212 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161213 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161212 real P x). Qed.
Lemma lem5161214 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5161213 s x). Qed.
Lemma lem5161215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161216 (s : real -> Prop) (x : real) : (term47 x s) = (term48 s x).
Proof. exact (MK_COMB (@lem5161215) (@lem5161214 s x)). Qed.
Lemma lem5161218 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161219 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161218 real P x). Qed.
Lemma lem5161220 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5161219 t x). Qed.
Lemma lem5161221 (s : real -> Prop) (t : real -> Prop) (x : real) : (term55 s x t) = (term56 s t x).
Proof. exact (MK_COMB (@lem5161216 s x) (@lem5161220 t x)). Qed.
Lemma lem5161224 (s : real -> Prop) (t : real -> Prop) : (term57 s t) = (term58 s t).
Proof. exact (fun_ext (fun x : real => @lem5161221 s t x)). Qed.
Lemma lem5161225 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161226 (s : real -> Prop) (t : real -> Prop) : (term18 s t) = (term59 s t).
Proof. exact (MK_COMB (@lem5161225) (@lem5161224 s t)). Qed.
Lemma lem5161231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161232 (s : real -> Prop) (t : real -> Prop) : (term20 s t) = (term60 s t).
Proof. exact (MK_COMB (@lem5161231) (@lem5161226 s t)). Qed.
Lemma lem5161240 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161241 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161240 real P x). Qed.
Lemma lem5161242 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5161241 s x). Qed.
Lemma lem5161243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5161244 (s : real -> Prop) (x : real) : (term61 x s) = (term62 s x).
Proof. exact (MK_COMB (@lem5161243) (@lem5161242 s x)). Qed.
Lemma lem5161246 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5161247 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5161246 real x). Qed.
Lemma lem5161248 (s : real -> Prop) (x : real) : ((@IN real x s) = (@IN real x (@EMPTY real))) = ((s x) = False).
Proof. exact (MK_COMB (@lem5161244 s x) (@lem5161247 x)). Qed.
Lemma lem5161250 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5161251 (s : real -> Prop) (x : real) : ((s x) = False) = (term63 s x).
Proof. exact (@lem5161250 (s x)). Qed.
Lemma lem5161252 (s : real -> Prop) (x : real) : ((@IN real x s) = (@IN real x (@EMPTY real))) = (term63 s x).
Proof. exact (TRANS (@lem5161248 s x) (@lem5161251 s x)). Qed.
Lemma lem5161253 (s : real -> Prop) : (term64 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5161252 s x)). Qed.
Lemma lem5161254 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161255 (s : real -> Prop) : (term23 s) = (term66 s).
Proof. exact (MK_COMB (@lem5161254) (@lem5161253 s)). Qed.
Lemma lem5161260 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161261 (s : real -> Prop) : (term24 s) = (term67 s).
Proof. exact (MK_COMB (@lem5161260) (@lem5161255 s)). Qed.
Lemma lem5161262 (t : real -> Prop) (s : real -> Prop) : (term25 t s) = (term68 t s).
Proof. exact (MK_COMB (@lem5161232 s t) (@lem5161261 s)). Qed.
Lemma lem5161265 (b : real) (t : real -> Prop) (s : real -> Prop) : (term27 b t s) = (term69 b t s).
Proof. exact (MK_COMB (@lem5161202 t b) (@lem5161262 t s)). Qed.
Lemma lem5161268 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161269 (b : real) (t : real -> Prop) (s : real -> Prop) : (term29 b t s) = (term70 b t s).
Proof. exact (MK_COMB (@lem5161268) (@lem5161265 b t s)). Qed.
Lemma lem5161283 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161284 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161283 real P x). Qed.
Lemma lem5161285 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5161284 t x). Qed.
Lemma lem5161286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5161287 (t : real -> Prop) (x : real) : (term61 x t) = (term62 t x).
Proof. exact (MK_COMB (@lem5161286) (@lem5161285 t x)). Qed.
Lemma lem5161289 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5161290 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5161289 real x). Qed.
Lemma lem5161291 (t : real -> Prop) (x : real) : ((@IN real x t) = (@IN real x (@EMPTY real))) = ((t x) = False).
Proof. exact (MK_COMB (@lem5161287 t x) (@lem5161290 x)). Qed.
Lemma lem5161293 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5161294 (t : real -> Prop) (x : real) : ((t x) = False) = (term63 t x).
Proof. exact (@lem5161293 (t x)). Qed.
Lemma lem5161295 (t : real -> Prop) (x : real) : ((@IN real x t) = (@IN real x (@EMPTY real))) = (term63 t x).
Proof. exact (TRANS (@lem5161291 t x) (@lem5161294 t x)). Qed.
Lemma lem5161296 (t : real -> Prop) : (term64 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5161295 t x)). Qed.
Lemma lem5161297 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161298 (t : real -> Prop) : (term23 t) = (term66 t).
Proof. exact (MK_COMB (@lem5161297) (@lem5161296 t)). Qed.
Lemma lem5161303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161304 (t : real -> Prop) : (term24 t) = (term67 t).
Proof. exact (MK_COMB (@lem5161303) (@lem5161298 t)). Qed.
Lemma lem5161305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161306 (t : real -> Prop) : (term31 t) = (term71 t).
Proof. exact (MK_COMB (@lem5161305) (@lem5161304 t)). Qed.
Lemma lem5161318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161319 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161318 real P x). Qed.
Lemma lem5161320 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5161319 t x). Qed.
Lemma lem5161321 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161322 (t : real -> Prop) (x : real) : (term47 x t) = (term48 t x).
Proof. exact (MK_COMB (@lem5161321) (@lem5161320 t x)). Qed.
Lemma lem5161323 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5161324 (t : real -> Prop) (x : real) (b : real) : (term49 t x b) = (term50 t x b).
Proof. exact (MK_COMB (@lem5161322 t x) (@lem5161323 x b)). Qed.
Lemma lem5161327 (t : real -> Prop) (b : real) : (term51 t b) = (term52 t b).
Proof. exact (fun_ext (fun x : real => @lem5161324 t x b)). Qed.
Lemma lem5161328 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161329 (t : real -> Prop) (b : real) : (term13 t b) = (term53 t b).
Proof. exact (MK_COMB (@lem5161328) (@lem5161327 t b)). Qed.
Lemma lem5161334 (t : real -> Prop) : (term72 t) = (term73 t).
Proof. exact (fun_ext (fun b : real => @lem5161329 t b)). Qed.
Lemma lem5161335 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5161336 (t : real -> Prop) : (term12 t) = (term74 t).
Proof. exact (MK_COMB (@lem5161335) (@lem5161334 t)). Qed.
Lemma lem5161341 (t : real -> Prop) : (term33 t) = (term75 t).
Proof. exact (MK_COMB (@lem5161306 t) (@lem5161336 t)). Qed.
Lemma lem5161344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161345 (t : real -> Prop) : (term35 t) = (term76 t).
Proof. exact (MK_COMB (@lem5161344) (@lem5161341 t)). Qed.
Lemma lem5161355 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161356 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161355 real P x). Qed.
Lemma lem5161357 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5161356 t x). Qed.
Lemma lem5161358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161359 (t : real -> Prop) (x : real) : (term47 x t) = (term48 t x).
Proof. exact (MK_COMB (@lem5161358) (@lem5161357 t x)). Qed.
Lemma lem5161360 (x : real) (t : real -> Prop) : (term77 x t) = (term77 x t).
Proof. exact (eq_refl (term77 x t)). Qed.
Lemma lem5161361 (x : real) (t : real -> Prop) : (term78 x t) = (term79 x t).
Proof. exact (MK_COMB (@lem5161359 t x) (@lem5161360 x t)). Qed.
Lemma lem5161364 (t : real -> Prop) : (term80 t) = (term81 t).
Proof. exact (fun_ext (fun x : real => @lem5161361 x t)). Qed.
Lemma lem5161365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161366 (t : real -> Prop) : (term82 t) = (term83 t).
Proof. exact (MK_COMB (@lem5161365) (@lem5161364 t)). Qed.
Lemma lem5161371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161372 (t : real -> Prop) : (term84 t) = (term85 t).
Proof. exact (MK_COMB (@lem5161371) (@lem5161366 t)). Qed.
Lemma lem5161386 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161387 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161386 real P x). Qed.
Lemma lem5161388 (t : real -> Prop) (x : real) : (@IN real x t) = (t x).
Proof. exact (@lem5161387 t x). Qed.
Lemma lem5161389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161390 (t : real -> Prop) (x : real) : (term47 x t) = (term48 t x).
Proof. exact (MK_COMB (@lem5161389) (@lem5161388 t x)). Qed.
Lemma lem5161391 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5161392 (t : real -> Prop) (x : real) (b : real) : (term49 t x b) = (term50 t x b).
Proof. exact (MK_COMB (@lem5161390 t x) (@lem5161391 x b)). Qed.
Lemma lem5161395 (t : real -> Prop) (b : real) : (term51 t b) = (term52 t b).
Proof. exact (fun_ext (fun x : real => @lem5161392 t x b)). Qed.
Lemma lem5161396 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161397 (t : real -> Prop) (b : real) : (term13 t b) = (term53 t b).
Proof. exact (MK_COMB (@lem5161396) (@lem5161395 t b)). Qed.
Lemma lem5161402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161403 (t : real -> Prop) (b : real) : (term86 t b) = (term87 t b).
Proof. exact (MK_COMB (@lem5161402) (@lem5161397 t b)). Qed.
Lemma lem5161404 (t : real -> Prop) (b : real) : (term6 t b) = (term6 t b).
Proof. exact (eq_refl (term6 t b)). Qed.
Lemma lem5161405 (t : real -> Prop) (b : real) : (term88 t b) = (term89 t b).
Proof. exact (MK_COMB (@lem5161403 t b) (@lem5161404 t b)). Qed.
Lemma lem5161408 (t : real -> Prop) : (term90 t) = (term91 t).
Proof. exact (fun_ext (fun b : real => @lem5161405 t b)). Qed.
Lemma lem5161409 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161410 (t : real -> Prop) : (term92 t) = (term93 t).
Proof. exact (MK_COMB (@lem5161409) (@lem5161408 t)). Qed.
Lemma lem5161415 (t : real -> Prop) : (term36 t) = (term94 t).
Proof. exact (MK_COMB (@lem5161372 t) (@lem5161410 t)). Qed.
Lemma lem5161418 (t : real -> Prop) : (term37 t) = (term95 t).
Proof. exact (MK_COMB (@lem5161345 t) (@lem5161415 t)). Qed.
Lemma lem5161421 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161422 (t : real -> Prop) : (term39 t) = (term96 t).
Proof. exact (MK_COMB (@lem5161421) (@lem5161418 t)). Qed.
Lemma lem5161432 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161433 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161432 real P x). Qed.
Lemma lem5161434 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5161433 s x). Qed.
Lemma lem5161435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5161436 (s : real -> Prop) (x : real) : (term61 x s) = (term62 s x).
Proof. exact (MK_COMB (@lem5161435) (@lem5161434 s x)). Qed.
Lemma lem5161438 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5161439 (x : real) : (@IN real x (@EMPTY real)) = False.
Proof. exact (@lem5161438 real x). Qed.
Lemma lem5161440 (s : real -> Prop) (x : real) : ((@IN real x s) = (@IN real x (@EMPTY real))) = ((s x) = False).
Proof. exact (MK_COMB (@lem5161436 s x) (@lem5161439 x)). Qed.
Lemma lem5161442 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5161443 (s : real -> Prop) (x : real) : ((s x) = False) = (term63 s x).
Proof. exact (@lem5161442 (s x)). Qed.
Lemma lem5161444 (s : real -> Prop) (x : real) : ((@IN real x s) = (@IN real x (@EMPTY real))) = (term63 s x).
Proof. exact (TRANS (@lem5161440 s x) (@lem5161443 s x)). Qed.
Lemma lem5161445 (s : real -> Prop) : (term64 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5161444 s x)). Qed.
Lemma lem5161446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161447 (s : real -> Prop) : (term23 s) = (term66 s).
Proof. exact (MK_COMB (@lem5161446) (@lem5161445 s)). Qed.
Lemma lem5161452 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161453 (s : real -> Prop) : (term24 s) = (term67 s).
Proof. exact (MK_COMB (@lem5161452) (@lem5161447 s)). Qed.
Lemma lem5161454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161455 (s : real -> Prop) : (term31 s) = (term71 s).
Proof. exact (MK_COMB (@lem5161454) (@lem5161453 s)). Qed.
Lemma lem5161463 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5161464 (P : real -> Prop) (x : real) : (@IN real x P) = (P x).
Proof. exact (@lem5161463 real P x). Qed.
Lemma lem5161465 (s : real -> Prop) (x : real) : (@IN real x s) = (s x).
Proof. exact (@lem5161464 s x). Qed.
Lemma lem5161466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161467 (s : real -> Prop) (x : real) : (term47 x s) = (term48 s x).
Proof. exact (MK_COMB (@lem5161466) (@lem5161465 s x)). Qed.
Lemma lem5161468 (x : real) (t : real -> Prop) : (term77 x t) = (term77 x t).
Proof. exact (eq_refl (term77 x t)). Qed.
Lemma lem5161469 (s : real -> Prop) (x : real) (t : real -> Prop) : (term97 s x t) = (term98 s x t).
Proof. exact (MK_COMB (@lem5161467 s x) (@lem5161468 x t)). Qed.
Lemma lem5161472 (s : real -> Prop) (t : real -> Prop) : (term99 s t) = (term100 s t).
Proof. exact (fun_ext (fun x : real => @lem5161469 s x t)). Qed.
Lemma lem5161473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161474 (s : real -> Prop) (t : real -> Prop) : (term40 s t) = (term101 s t).
Proof. exact (MK_COMB (@lem5161473) (@lem5161472 s t)). Qed.
Lemma lem5161479 (s : real -> Prop) (t : real -> Prop) : (term42 s t) = (term102 s t).
Proof. exact (MK_COMB (@lem5161455 s) (@lem5161474 s t)). Qed.
Lemma lem5161482 (s : real -> Prop) (t : real -> Prop) : (term44 s t) = (term103 s t).
Proof. exact (MK_COMB (@lem5161422 t) (@lem5161479 s t)). Qed.
Lemma lem5161485 (b : real) (s : real -> Prop) (t : real -> Prop) : (term46 b s t) = (term104 b s t).
Proof. exact (MK_COMB (@lem5161269 b t s) (@lem5161482 s t)). Qed.
Lemma lem5161488 (b : real) (s : real -> Prop) (t : real -> Prop) : (term104 b s t) = (term46 b s t).
Proof. exact (SYM (@lem5161485 b s t)). Qed.
Lemma lem5161490 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5161491 (b : real) (s : real -> Prop) (t : real -> Prop) : (term104 b s t) = (term106 b s t).
Proof. exact (@lem5161490 (term104 b s t)). Qed.
Lemma lem5161492 (b : real) (s : real -> Prop) (t : real -> Prop) : (term106 b s t) = (term104 b s t).
Proof. exact (SYM (@lem5161491 b s t)). Qed.
Lemma lem5161493 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term107 b s t) : term107 b s t.
Proof. exact (h1). Qed.
Lemma lem5161496 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term106 b s t) : term106 b s t.
Proof. exact (h1). Qed.
Lemma lem5161497 (b : real) (s : real -> Prop) (t : real -> Prop) : term108 b s t.
Proof. exact (fun h0 : term106 b s t => @lem5161496 b s t h0). Qed.
Lemma lem5161498 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term108 b s t) : term108 b s t.
Proof. exact (h1). Qed.
Lemma lem5161499 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term106 b s t) : term106 b s t.
Proof. exact (h1). Qed.
Lemma lem5161500 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term106 b s t) (h2 : term108 b s t) : term106 b s t.
Proof. exact (@lem5161498 b s t h2 (@lem5161499 b s t h1)). Qed.
Lemma lem5161501 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term106 b s t) : term109 b s t.
Proof. exact (fun h0 : term108 b s t => @lem5161500 b s t h1 h0). Qed.
Lemma lem5161502 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term108 b s t) : term108 b s t.
Proof. exact (h1). Qed.
Lemma lem5161503 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term106 b s t) (h2 : term108 b s t) : term106 b s t.
Proof. exact (@lem5161501 b s t h1 (@lem5161502 b s t h2)). Qed.
Lemma lem5161504 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term108 b s t) : term108 b s t.
Proof. exact (fun h0 : term106 b s t => @lem5161503 b s t h0 h1). Qed.
Lemma lem5161505 (b : real) (s : real -> Prop) (t : real -> Prop) : term110 b s t.
Proof. exact (fun h0 : term108 b s t => @lem5161504 b s t h0). Qed.
Lemma lem5161508 (b : real) (s : real -> Prop) (t : real -> Prop) : term108 b s t.
Proof. exact (@lem5161505 b s t (@lem5161497 b s t)). Qed.
Lemma lem5161522 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5161523 (b : real) (s : real -> Prop) (t : real -> Prop) : (term106 b s t) = (term111 b s t).
Proof. exact (@lem5161522 (term107 b s t)). Qed.
Lemma lem5161525 (t : Prop) : (term112 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5161526 (b : real) (s : real -> Prop) (t : real -> Prop) : (term111 b s t) = (term104 b s t).
Proof. exact (@lem5161525 (term104 b s t)). Qed.
Lemma lem5161529 (b : real) (s : real -> Prop) (t : real -> Prop) : (term106 b s t) = (term104 b s t).
Proof. exact (TRANS (@lem5161523 b s t) (@lem5161526 b s t)). Qed.
Lemma lem5161602 (s : real -> Prop) (t : real -> Prop) : (term113 s t) = (term114 s t).
Proof. exact (fun_ext (fun b : real => @lem5161529 b s t)). Qed.
Lemma lem5161603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161604 (s : real -> Prop) (t : real -> Prop) : (term115 s t) = (term116 s t).
Proof. exact (MK_COMB (@lem5161603) (@lem5161602 s t)). Qed.
Lemma lem5161609 (t : real -> Prop) : (term117 t) = (term118 t).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5161604 s t)). Qed.
Lemma lem5161610 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5161611 (t : real -> Prop) : (term119 t) = (term120 t).
Proof. exact (MK_COMB (@lem5161610) (@lem5161609 t)). Qed.
Lemma lem5161616 : term121 = term122.
Proof. exact (fun_ext (fun t : real -> Prop => @lem5161611 t)). Qed.
Lemma lem5161617 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5161626 : term123 = term124.
Proof. exact (MK_COMB (@lem5161617) (@lem5161616)). Qed.
Lemma lem5161631 (s : real -> Prop) (x : real) (t : real -> Prop) : (term98 s x t) = (term98 s x t).
Proof. exact (eq_refl (term98 s x t)). Qed.
Lemma lem5161632 (s : real -> Prop) (t : real -> Prop) : (term100 s t) = (term100 s t).
Proof. exact (fun_ext (fun x : real => @lem5161631 s x t)). Qed.
Lemma lem5161633 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161634 (s : real -> Prop) (t : real -> Prop) : (term101 s t) = (term101 s t).
Proof. exact (MK_COMB (@lem5161633) (@lem5161632 s t)). Qed.
Lemma lem5161637 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5161638 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5161637 s x)). Qed.
Lemma lem5161639 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161640 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5161639) (@lem5161638 s)). Qed.
Lemma lem5161641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161642 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (MK_COMB (@lem5161641) (@lem5161640 s)). Qed.
Lemma lem5161643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161644 (s : real -> Prop) : (term71 s) = (term71 s).
Proof. exact (MK_COMB (@lem5161643) (@lem5161642 s)). Qed.
Lemma lem5161645 (s : real -> Prop) (t : real -> Prop) : (term102 s t) = (term102 s t).
Proof. exact (MK_COMB (@lem5161644 s) (@lem5161634 s t)). Qed.
Lemma lem5161646 (t : real -> Prop) (b : real) : (term6 t b) = (term6 t b).
Proof. exact (eq_refl (term6 t b)). Qed.
Lemma lem5161651 (t : real -> Prop) (x : real) (b : real) : (term50 t x b) = (term50 t x b).
Proof. exact (eq_refl (term50 t x b)). Qed.
Lemma lem5161652 (t : real -> Prop) (b : real) : (term52 t b) = (term52 t b).
Proof. exact (fun_ext (fun x : real => @lem5161651 t x b)). Qed.
Lemma lem5161653 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161654 (t : real -> Prop) (b : real) : (term53 t b) = (term53 t b).
Proof. exact (MK_COMB (@lem5161653) (@lem5161652 t b)). Qed.
Lemma lem5161655 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161656 (t : real -> Prop) (b : real) : (term87 t b) = (term87 t b).
Proof. exact (MK_COMB (@lem5161655) (@lem5161654 t b)). Qed.
Lemma lem5161657 (t : real -> Prop) (b : real) : (term89 t b) = (term89 t b).
Proof. exact (MK_COMB (@lem5161656 t b) (@lem5161646 t b)). Qed.
Lemma lem5161658 (t : real -> Prop) : (term91 t) = (term91 t).
Proof. exact (fun_ext (fun b : real => @lem5161657 t b)). Qed.
Lemma lem5161659 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161660 (t : real -> Prop) : (term93 t) = (term93 t).
Proof. exact (MK_COMB (@lem5161659) (@lem5161658 t)). Qed.
Lemma lem5161665 (x : real) (t : real -> Prop) : (term79 x t) = (term79 x t).
Proof. exact (eq_refl (term79 x t)). Qed.
Lemma lem5161666 (t : real -> Prop) : (term81 t) = (term81 t).
Proof. exact (fun_ext (fun x : real => @lem5161665 x t)). Qed.
Lemma lem5161667 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161668 (t : real -> Prop) : (term83 t) = (term83 t).
Proof. exact (MK_COMB (@lem5161667) (@lem5161666 t)). Qed.
Lemma lem5161669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161670 (t : real -> Prop) : (term85 t) = (term85 t).
Proof. exact (MK_COMB (@lem5161669) (@lem5161668 t)). Qed.
Lemma lem5161671 (t : real -> Prop) : (term94 t) = (term94 t).
Proof. exact (MK_COMB (@lem5161670 t) (@lem5161660 t)). Qed.
Lemma lem5161676 (t : real -> Prop) (x : real) (b : real) : (term50 t x b) = (term50 t x b).
Proof. exact (eq_refl (term50 t x b)). Qed.
Lemma lem5161677 (t : real -> Prop) (b : real) : (term52 t b) = (term52 t b).
Proof. exact (fun_ext (fun x : real => @lem5161676 t x b)). Qed.
Lemma lem5161678 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161679 (t : real -> Prop) (b : real) : (term53 t b) = (term53 t b).
Proof. exact (MK_COMB (@lem5161678) (@lem5161677 t b)). Qed.
Lemma lem5161680 (t : real -> Prop) : (term73 t) = (term73 t).
Proof. exact (fun_ext (fun b : real => @lem5161679 t b)). Qed.
Lemma lem5161681 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5161682 (t : real -> Prop) : (term74 t) = (term74 t).
Proof. exact (MK_COMB (@lem5161681) (@lem5161680 t)). Qed.
Lemma lem5161685 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5161686 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5161685 t x)). Qed.
Lemma lem5161687 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161688 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5161687) (@lem5161686 t)). Qed.
Lemma lem5161689 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161690 (t : real -> Prop) : (term67 t) = (term67 t).
Proof. exact (MK_COMB (@lem5161689) (@lem5161688 t)). Qed.
Lemma lem5161691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161692 (t : real -> Prop) : (term71 t) = (term71 t).
Proof. exact (MK_COMB (@lem5161691) (@lem5161690 t)). Qed.
Lemma lem5161693 (t : real -> Prop) : (term75 t) = (term75 t).
Proof. exact (MK_COMB (@lem5161692 t) (@lem5161682 t)). Qed.
Lemma lem5161694 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161695 (t : real -> Prop) : (term76 t) = (term76 t).
Proof. exact (MK_COMB (@lem5161694) (@lem5161693 t)). Qed.
Lemma lem5161696 (t : real -> Prop) : (term95 t) = (term95 t).
Proof. exact (MK_COMB (@lem5161695 t) (@lem5161671 t)). Qed.
Lemma lem5161697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161698 (t : real -> Prop) : (term96 t) = (term96 t).
Proof. exact (MK_COMB (@lem5161697) (@lem5161696 t)). Qed.
Lemma lem5161699 (s : real -> Prop) (t : real -> Prop) : (term103 s t) = (term103 s t).
Proof. exact (MK_COMB (@lem5161698 t) (@lem5161645 s t)). Qed.
Lemma lem5161702 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5161703 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5161702 s x)). Qed.
Lemma lem5161704 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161705 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5161704) (@lem5161703 s)). Qed.
Lemma lem5161706 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161707 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (MK_COMB (@lem5161706) (@lem5161705 s)). Qed.
Lemma lem5161712 (s : real -> Prop) (t : real -> Prop) (x : real) : (term56 s t x) = (term56 s t x).
Proof. exact (eq_refl (term56 s t x)). Qed.
Lemma lem5161713 (s : real -> Prop) (t : real -> Prop) : (term58 s t) = (term58 s t).
Proof. exact (fun_ext (fun x : real => @lem5161712 s t x)). Qed.
Lemma lem5161714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161715 (s : real -> Prop) (t : real -> Prop) : (term59 s t) = (term59 s t).
Proof. exact (MK_COMB (@lem5161714) (@lem5161713 s t)). Qed.
Lemma lem5161716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161717 (s : real -> Prop) (t : real -> Prop) : (term60 s t) = (term60 s t).
Proof. exact (MK_COMB (@lem5161716) (@lem5161715 s t)). Qed.
Lemma lem5161718 (t : real -> Prop) (s : real -> Prop) : (term68 t s) = (term68 t s).
Proof. exact (MK_COMB (@lem5161717 s t) (@lem5161707 s)). Qed.
Lemma lem5161723 (t : real -> Prop) (x : real) (b : real) : (term50 t x b) = (term50 t x b).
Proof. exact (eq_refl (term50 t x b)). Qed.
Lemma lem5161724 (t : real -> Prop) (b : real) : (term52 t b) = (term52 t b).
Proof. exact (fun_ext (fun x : real => @lem5161723 t x b)). Qed.
Lemma lem5161725 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161726 (t : real -> Prop) (b : real) : (term53 t b) = (term53 t b).
Proof. exact (MK_COMB (@lem5161725) (@lem5161724 t b)). Qed.
Lemma lem5161727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161728 (t : real -> Prop) (b : real) : (term54 t b) = (term54 t b).
Proof. exact (MK_COMB (@lem5161727) (@lem5161726 t b)). Qed.
Lemma lem5161729 (b : real) (t : real -> Prop) (s : real -> Prop) : (term69 b t s) = (term69 b t s).
Proof. exact (MK_COMB (@lem5161728 t b) (@lem5161718 t s)). Qed.
Lemma lem5161730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5161731 (b : real) (t : real -> Prop) (s : real -> Prop) : (term70 b t s) = (term70 b t s).
Proof. exact (MK_COMB (@lem5161730) (@lem5161729 b t s)). Qed.
Lemma lem5161732 (b : real) (s : real -> Prop) (t : real -> Prop) : (term104 b s t) = (term104 b s t).
Proof. exact (MK_COMB (@lem5161731 b t s) (@lem5161699 s t)). Qed.
Lemma lem5161733 (s : real -> Prop) (t : real -> Prop) : (term114 s t) = (term114 s t).
Proof. exact (fun_ext (fun b : real => @lem5161732 b s t)). Qed.
Lemma lem5161734 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161735 (s : real -> Prop) (t : real -> Prop) : (term116 s t) = (term116 s t).
Proof. exact (MK_COMB (@lem5161734) (@lem5161733 s t)). Qed.
Lemma lem5161736 (t : real -> Prop) : (term118 t) = (term118 t).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5161735 s t)). Qed.
Lemma lem5161737 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5161738 (t : real -> Prop) : (term120 t) = (term120 t).
Proof. exact (MK_COMB (@lem5161737) (@lem5161736 t)). Qed.
Lemma lem5161739 : term122 = term122.
Proof. exact (fun_ext (fun t : real -> Prop => @lem5161738 t)). Qed.
Lemma lem5161740 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5161741 : term124 = term124.
Proof. exact (MK_COMB (@lem5161740) (@lem5161739)). Qed.
Lemma lem5161858 : term123 = term124.
Proof. exact (TRANS (@lem5161626) (@lem5161741)). Qed.
Lemma lem5161859 : term124 = term123.
Proof. exact (SYM (@lem5161858)). Qed.
Lemma lem5161860 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term69 b t s) : term69 b t s.
Proof. exact (h1). Qed.
Lemma lem5161861 (t : real -> Prop) (h1 : term95 t) : term95 t.
Proof. exact (h1). Qed.
Lemma lem5161863 (p : Prop) : p = (term105 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5161864 (s : real -> Prop) (t : real -> Prop) : (term102 s t) = (term125 s t).
Proof. exact (@lem5161863 (term102 s t)). Qed.
Lemma lem5161865 (s : real -> Prop) (t : real -> Prop) : (term125 s t) = (term102 s t).
Proof. exact (SYM (@lem5161864 s t)). Qed.
Lemma lem5161866 (s : real -> Prop) (t : real -> Prop) (h1 : term126 s t) : term126 s t.
Proof. exact (h1). Qed.
Lemma lem5161873 (t : real -> Prop) (x : real) (b : real) : (term50 t x b) = (term127 t x b).
Proof. exact (@lem17265 (t x) (real_le x b)). Qed.
Lemma lem5161874 (t : real -> Prop) (b : real) : (term52 t b) = (term128 t b).
Proof. exact (fun_ext (fun x : real => @lem5161873 t x b)). Qed.
Lemma lem5161875 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161876 (t : real -> Prop) (b : real) : (term53 t b) = (term129 t b).
Proof. exact (MK_COMB (@lem5161875) (@lem5161874 t b)). Qed.
Lemma lem5161883 (s : real -> Prop) (t : real -> Prop) (x : real) : (term56 s t x) = (term130 s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem5161884 (s : real -> Prop) (t : real -> Prop) : (term58 s t) = (term131 s t).
Proof. exact (fun_ext (fun x : real => @lem5161883 s t x)). Qed.
Lemma lem5161885 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5161886 (s : real -> Prop) (t : real -> Prop) : (term59 s t) = (term132 s t).
Proof. exact (MK_COMB (@lem5161885) (@lem5161884 s t)). Qed.
Lemma lem5161889 (s : real -> Prop) (x : real) : (term133 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem5161890 (P : real -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5161891 (s : real -> Prop) : (term67 s) = (term136 s).
Proof. exact (@lem5161890 (term65 s)). Qed.
Lemma lem5161892 (s : real -> Prop) (x : real) : (term137 s x) = (term63 s x).
Proof. exact (eq_refl (term137 s x)). Qed.
Lemma lem5161893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5161894 (s : real -> Prop) (x : real) : (term138 s x) = (term133 s x).
Proof. exact (MK_COMB (@lem5161893) (@lem5161892 s x)). Qed.
Lemma lem5161895 (s : real -> Prop) (x : real) : (term138 s x) = (s x).
Proof. exact (TRANS (@lem5161894 s x) (@lem5161889 s x)). Qed.
Lemma lem5161896 (s : real -> Prop) : (term139 s) = (term140 s).
Proof. exact (fun_ext (fun x : real => @lem5161895 s x)). Qed.
Lemma lem5161897 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5161898 (s : real -> Prop) : (term136 s) = (term141 s).
Proof. exact (MK_COMB (@lem5161897) (@lem5161896 s)). Qed.
Lemma lem5161899 (s : real -> Prop) : (term67 s) = (term141 s).
Proof. exact (TRANS (@lem5161891 s) (@lem5161898 s)). Qed.
Lemma lem5161900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161901 (s : real -> Prop) (t : real -> Prop) : (term60 s t) = (term142 s t).
Proof. exact (MK_COMB (@lem5161900) (@lem5161886 s t)). Qed.
Lemma lem5161902 (t : real -> Prop) (s : real -> Prop) : (term68 t s) = (term143 t s).
Proof. exact (MK_COMB (@lem5161901 s t) (@lem5161899 s)). Qed.
Lemma lem5161903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5161904 (t : real -> Prop) (b : real) : (term54 t b) = (term144 t b).
Proof. exact (MK_COMB (@lem5161903) (@lem5161876 t b)). Qed.
Lemma lem5161905 (b : real) (t : real -> Prop) (s : real -> Prop) : (term69 b t s) = (term145 b t s).
Proof. exact (MK_COMB (@lem5161904 t b) (@lem5161902 t s)). Qed.
Lemma lem5161992 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5161993 (P : Prop) (Q : real -> Prop) : (term148 P Q) = (term149 P Q).
Proof. exact (@lem5161992 real P Q). Qed.
Lemma lem5161994 (t : real -> Prop) (s : real -> Prop) : (term143 t s) = (term150 t s).
Proof. exact (@lem5161993 (term132 s t) s). Qed.
Lemma lem5161995 (t : real -> Prop) (b : real) : (term144 t b) = (term144 t b).
Proof. exact (eq_refl (term144 t b)). Qed.
Lemma lem5161996 (b : real) (t : real -> Prop) (s : real -> Prop) : (term145 b t s) = (term151 b t s).
Proof. exact (MK_COMB (@lem5161995 t b) (@lem5161994 t s)). Qed.
Lemma lem5161998 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5161999 (P : Prop) (Q : real -> Prop) : (term148 P Q) = (term149 P Q).
Proof. exact (@lem5161998 real P Q). Qed.
Lemma lem5162000 (b : real) (t : real -> Prop) (s : real -> Prop) : (term152 b t s) = (term153 b t s).
Proof. exact (@lem5161999 (term129 t b) (term154 t s)). Qed.
Lemma lem5162001 (t : real -> Prop) (s : real -> Prop) (x : real) : (term155 t s x) = (term156 t s x).
Proof. exact (eq_refl (term155 t s x)). Qed.
Lemma lem5162002 (t : real -> Prop) (s : real -> Prop) : (term157 t s) = (term154 t s).
Proof. exact (fun_ext (fun x : real => @lem5162001 t s x)). Qed.
Lemma lem5162003 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162004 (t : real -> Prop) (s : real -> Prop) : (term158 t s) = (term150 t s).
Proof. exact (MK_COMB (@lem5162003) (@lem5162002 t s)). Qed.
Lemma lem5162005 (t : real -> Prop) (b : real) : (term144 t b) = (term144 t b).
Proof. exact (eq_refl (term144 t b)). Qed.
Lemma lem5162006 (b : real) (t : real -> Prop) (s : real -> Prop) : (term152 b t s) = (term151 b t s).
Proof. exact (MK_COMB (@lem5162005 t b) (@lem5162004 t s)). Qed.
Lemma lem5162007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5162008 (b : real) (t : real -> Prop) (s : real -> Prop) : (term159 b t s) = (term160 b t s).
Proof. exact (MK_COMB (@lem5162007) (@lem5162006 b t s)). Qed.
Lemma lem5162009 (t : real -> Prop) (s : real -> Prop) (x : real) : (term155 t s x) = (term156 t s x).
Proof. exact (eq_refl (term155 t s x)). Qed.
Lemma lem5162010 (t : real -> Prop) (b : real) : (term144 t b) = (term144 t b).
Proof. exact (eq_refl (term144 t b)). Qed.
Lemma lem5162011 (b : real) (t : real -> Prop) (s : real -> Prop) (x : real) : (term161 b t s x) = (term162 b t s x).
Proof. exact (MK_COMB (@lem5162010 t b) (@lem5162009 t s x)). Qed.
Lemma lem5162012 (b : real) (t : real -> Prop) (s : real -> Prop) : (term163 b t s) = (term164 b t s).
Proof. exact (fun_ext (fun x : real => @lem5162011 b t s x)). Qed.
Lemma lem5162013 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162014 (b : real) (t : real -> Prop) (s : real -> Prop) : (term153 b t s) = (term165 b t s).
Proof. exact (MK_COMB (@lem5162013) (@lem5162012 b t s)). Qed.
Lemma lem5162015 (b : real) (t : real -> Prop) (s : real -> Prop) : ((term152 b t s) = (term153 b t s)) = ((term151 b t s) = (term165 b t s)).
Proof. exact (MK_COMB (@lem5162008 b t s) (@lem5162014 b t s)). Qed.
Lemma lem5162016 (b : real) (t : real -> Prop) (s : real -> Prop) : (term151 b t s) = (term165 b t s).
Proof. exact (EQ_MP (@lem5162015 b t s) (@lem5162000 b t s)). Qed.
Lemma lem5162018 (b : real) (t : real -> Prop) (s : real -> Prop) : (term145 b t s) = (term165 b t s).
Proof. exact (TRANS (@lem5161996 b t s) (@lem5162016 b t s)). Qed.
Lemma lem5162019 (b : real) (t : real -> Prop) (s : real -> Prop) : (term69 b t s) = (term165 b t s).
Proof. exact (TRANS (@lem5161905 b t s) (@lem5162018 b t s)). Qed.
Lemma lem5162020 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term69 b t s) : term165 b t s.
Proof. exact (EQ_MP (@lem5162019 b t s) (@lem5161860 b t s h1)). Qed.
Lemma lem5162021 (t : real -> Prop) (x : real) : (term63 t x) = (term63 t x).
Proof. exact (eq_refl (term63 t x)). Qed.
Lemma lem5162022 (t : real -> Prop) : (term65 t) = (term65 t).
Proof. exact (fun_ext (fun x : real => @lem5162021 t x)). Qed.
Lemma lem5162023 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162024 (t : real -> Prop) : (term66 t) = (term66 t).
Proof. exact (MK_COMB (@lem5162023) (@lem5162022 t)). Qed.
Lemma lem5162025 (t : real -> Prop) : (term166 t) = (term66 t).
Proof. exact (@lem16933 (term66 t)). Qed.
Lemma lem5162026 (t : real -> Prop) : (term166 t) = (term66 t).
Proof. exact (TRANS (@lem5162025 t) (@lem5162024 t)). Qed.
Lemma lem5162033 (t : real -> Prop) (x : real) (b : real) : (term167 t x b) = (term168 t x b).
Proof. exact (@lem17362 (t x) (real_le x b)). Qed.
Lemma lem5162034 (P : real -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5162035 (t : real -> Prop) (b : real) : (term169 t b) = (term170 t b).
Proof. exact (@lem5162034 (term52 t b)). Qed.
Lemma lem5162036 (t : real -> Prop) (x : real) (b : real) : (term171 t b x) = (term50 t x b).
Proof. exact (eq_refl (term171 t b x)). Qed.
Lemma lem5162037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5162038 (t : real -> Prop) (x : real) (b : real) : (term172 t b x) = (term167 t x b).
Proof. exact (MK_COMB (@lem5162037) (@lem5162036 t x b)). Qed.
Lemma lem5162039 (t : real -> Prop) (x : real) (b : real) : (term172 t b x) = (term168 t x b).
Proof. exact (TRANS (@lem5162038 t x b) (@lem5162033 t x b)). Qed.
Lemma lem5162040 (t : real -> Prop) (b : real) : (term173 t b) = (term174 t b).
Proof. exact (fun_ext (fun x : real => @lem5162039 t x b)). Qed.
Lemma lem5162041 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162042 (t : real -> Prop) (b : real) : (term170 t b) = (term175 t b).
Proof. exact (MK_COMB (@lem5162041) (@lem5162040 t b)). Qed.
Lemma lem5162043 (t : real -> Prop) (b : real) : (term169 t b) = (term175 t b).
Proof. exact (TRANS (@lem5162035 t b) (@lem5162042 t b)). Qed.
Lemma lem5162044 (P : real -> Prop) : (term176 P) = (term66 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5162045 (t : real -> Prop) : (term177 t) = (term178 t).
Proof. exact (@lem5162044 (term73 t)). Qed.
Lemma lem5162046 (t : real -> Prop) (b : real) : (term179 t b) = (term53 t b).
Proof. exact (eq_refl (term179 t b)). Qed.
Lemma lem5162047 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5162048 (t : real -> Prop) (b : real) : (term180 t b) = (term169 t b).
Proof. exact (MK_COMB (@lem5162047) (@lem5162046 t b)). Qed.
Lemma lem5162049 (t : real -> Prop) (b : real) : (term180 t b) = (term175 t b).
Proof. exact (TRANS (@lem5162048 t b) (@lem5162043 t b)). Qed.
Lemma lem5162050 (t : real -> Prop) : (term181 t) = (term182 t).
Proof. exact (fun_ext (fun b : real => @lem5162049 t b)). Qed.
Lemma lem5162051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162052 (t : real -> Prop) : (term178 t) = (term183 t).
Proof. exact (MK_COMB (@lem5162051) (@lem5162050 t)). Qed.
Lemma lem5162053 (t : real -> Prop) : (term177 t) = (term183 t).
Proof. exact (TRANS (@lem5162045 t) (@lem5162052 t)). Qed.
Lemma lem5162054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162055 (t : real -> Prop) : (term184 t) = (term185 t).
Proof. exact (MK_COMB (@lem5162054) (@lem5162026 t)). Qed.
Lemma lem5162056 (t : real -> Prop) : (term186 t) = (term187 t).
Proof. exact (MK_COMB (@lem5162055 t) (@lem5162053 t)). Qed.
Lemma lem5162057 (t : real -> Prop) : (term188 t) = (term186 t).
Proof. exact (@lem17045 (term67 t) (term74 t)). Qed.
Lemma lem5162058 (t : real -> Prop) : (term188 t) = (term187 t).
Proof. exact (TRANS (@lem5162057 t) (@lem5162056 t)). Qed.
Lemma lem5162065 (x : real) (t : real -> Prop) : (term79 x t) = (term189 x t).
Proof. exact (@lem17265 (t x) (term77 x t)). Qed.
Lemma lem5162066 (t : real -> Prop) : (term81 t) = (term190 t).
Proof. exact (fun_ext (fun x : real => @lem5162065 x t)). Qed.
Lemma lem5162067 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162068 (t : real -> Prop) : (term83 t) = (term191 t).
Proof. exact (MK_COMB (@lem5162067) (@lem5162066 t)). Qed.
Lemma lem5162075 (t : real -> Prop) (x : real) (b : real) : (term167 t x b) = (term168 t x b).
Proof. exact (@lem17362 (t x) (real_le x b)). Qed.
Lemma lem5162076 (P : real -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5162077 (t : real -> Prop) (b : real) : (term169 t b) = (term170 t b).
Proof. exact (@lem5162076 (term52 t b)). Qed.
Lemma lem5162078 (t : real -> Prop) (x : real) (b : real) : (term171 t b x) = (term50 t x b).
Proof. exact (eq_refl (term171 t b x)). Qed.
Lemma lem5162079 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5162080 (t : real -> Prop) (x : real) (b : real) : (term172 t b x) = (term167 t x b).
Proof. exact (MK_COMB (@lem5162079) (@lem5162078 t x b)). Qed.
Lemma lem5162081 (t : real -> Prop) (x : real) (b : real) : (term172 t b x) = (term168 t x b).
Proof. exact (TRANS (@lem5162080 t x b) (@lem5162075 t x b)). Qed.
Lemma lem5162082 (t : real -> Prop) (b : real) : (term173 t b) = (term174 t b).
Proof. exact (fun_ext (fun x : real => @lem5162081 t x b)). Qed.
Lemma lem5162083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162084 (t : real -> Prop) (b : real) : (term170 t b) = (term175 t b).
Proof. exact (MK_COMB (@lem5162083) (@lem5162082 t b)). Qed.
Lemma lem5162085 (t : real -> Prop) (b : real) : (term169 t b) = (term175 t b).
Proof. exact (TRANS (@lem5162077 t b) (@lem5162084 t b)). Qed.
Lemma lem5162086 (t : real -> Prop) (b : real) : (term6 t b) = (term6 t b).
Proof. exact (eq_refl (term6 t b)). Qed.
Lemma lem5162087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162088 (t : real -> Prop) (b : real) : (term192 t b) = (term193 t b).
Proof. exact (MK_COMB (@lem5162087) (@lem5162085 t b)). Qed.
Lemma lem5162089 (t : real -> Prop) (b : real) : (term194 t b) = (term195 t b).
Proof. exact (MK_COMB (@lem5162088 t b) (@lem5162086 t b)). Qed.
Lemma lem5162090 (t : real -> Prop) (b : real) : (term89 t b) = (term194 t b).
Proof. exact (@lem17265 (term53 t b) (term6 t b)). Qed.
Lemma lem5162091 (t : real -> Prop) (b : real) : (term89 t b) = (term195 t b).
Proof. exact (TRANS (@lem5162090 t b) (@lem5162089 t b)). Qed.
Lemma lem5162092 (t : real -> Prop) : (term91 t) = (term196 t).
Proof. exact (fun_ext (fun b : real => @lem5162091 t b)). Qed.
Lemma lem5162093 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162094 (t : real -> Prop) : (term93 t) = (term197 t).
Proof. exact (MK_COMB (@lem5162093) (@lem5162092 t)). Qed.
Lemma lem5162095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5162096 (t : real -> Prop) : (term85 t) = (term198 t).
Proof. exact (MK_COMB (@lem5162095) (@lem5162068 t)). Qed.
Lemma lem5162097 (t : real -> Prop) : (term94 t) = (term199 t).
Proof. exact (MK_COMB (@lem5162096 t) (@lem5162094 t)). Qed.
Lemma lem5162098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162099 (t : real -> Prop) : (term200 t) = (term201 t).
Proof. exact (MK_COMB (@lem5162098) (@lem5162058 t)). Qed.
Lemma lem5162100 (t : real -> Prop) : (term202 t) = (term203 t).
Proof. exact (MK_COMB (@lem5162099 t) (@lem5162097 t)). Qed.
Lemma lem5162101 (t : real -> Prop) : (term95 t) = (term202 t).
Proof. exact (@lem17265 (term75 t) (term94 t)). Qed.
Lemma lem5162102 (t : real -> Prop) : (term95 t) = (term203 t).
Proof. exact (TRANS (@lem5162101 t) (@lem5162100 t)). Qed.
Lemma lem5162265 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5162266 (P : type1626) : (term206 P) = (term207 P).
Proof. exact (@lem5162265 real real P). Qed.
Lemma lem5162267 (t : real -> Prop) : (term208 t) = (term209 t).
Proof. exact (@lem5162266 (term210 t)). Qed.
Lemma lem5162268 (t : real -> Prop) (b : real) : (term211 t b) = (term174 t b).
Proof. exact (eq_refl (term211 t b)). Qed.
Lemma lem5162269 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5162270 (t : real -> Prop) (b : real) (x : real) : (term212 t b x) = (term213 t b x).
Proof. exact (MK_COMB (@lem5162268 t b) (@lem5162269 x)). Qed.
Lemma lem5162271 (t : real -> Prop) (x : real) (b : real) : (term213 t b x) = (term168 t x b).
Proof. exact (eq_refl (term213 t b x)). Qed.
Lemma lem5162272 (t : real -> Prop) (x : real) (b : real) : (term212 t b x) = (term168 t x b).
Proof. exact (TRANS (@lem5162270 t b x) (@lem5162271 t x b)). Qed.
Lemma lem5162273 (t : real -> Prop) (b : real) : (term214 t b) = (term174 t b).
Proof. exact (fun_ext (fun x : real => @lem5162272 t x b)). Qed.
Lemma lem5162274 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162275 (t : real -> Prop) (b : real) : (term215 t b) = (term175 t b).
Proof. exact (MK_COMB (@lem5162274) (@lem5162273 t b)). Qed.
Lemma lem5162276 (t : real -> Prop) : (term216 t) = (term182 t).
Proof. exact (fun_ext (fun b : real => @lem5162275 t b)). Qed.
Lemma lem5162277 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162278 (t : real -> Prop) : (term208 t) = (term183 t).
Proof. exact (MK_COMB (@lem5162277) (@lem5162276 t)). Qed.
Lemma lem5162279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5162280 (t : real -> Prop) : (term217 t) = (term218 t).
Proof. exact (MK_COMB (@lem5162279) (@lem5162278 t)). Qed.
Lemma lem5162281 (t : real -> Prop) (b : real) : (term211 t b) = (term174 t b).
Proof. exact (eq_refl (term211 t b)). Qed.
Lemma lem5162282 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5162283 (t : real -> Prop) (x : real -> real) (b : real) : (term219 t x b) = (term220 t x b).
Proof. exact (MK_COMB (@lem5162281 t b) (@lem5162282 x b)). Qed.
Lemma lem5162284 (t : real -> Prop) (x : real -> real) (b : real) : (term220 t x b) = (term221 t x b).
Proof. exact (eq_refl (term220 t x b)). Qed.
Lemma lem5162285 (t : real -> Prop) (x : real -> real) (b : real) : (term219 t x b) = (term221 t x b).
Proof. exact (TRANS (@lem5162283 t x b) (@lem5162284 t x b)). Qed.
Lemma lem5162286 (t : real -> Prop) (x : real -> real) : (term222 t x) = (term223 t x).
Proof. exact (fun_ext (fun b : real => @lem5162285 t x b)). Qed.
Lemma lem5162287 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162288 (t : real -> Prop) (x : real -> real) : (term224 t x) = (term225 t x).
Proof. exact (MK_COMB (@lem5162287) (@lem5162286 t x)). Qed.
Lemma lem5162289 (t : real -> Prop) : (term226 t) = (term227 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162288 t x)). Qed.
Lemma lem5162290 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162291 (t : real -> Prop) : (term209 t) = (term228 t).
Proof. exact (MK_COMB (@lem5162290) (@lem5162289 t)). Qed.
Lemma lem5162292 (t : real -> Prop) : ((term208 t) = (term209 t)) = ((term183 t) = (term228 t)).
Proof. exact (MK_COMB (@lem5162280 t) (@lem5162291 t)). Qed.
Lemma lem5162293 (t : real -> Prop) : (term183 t) = (term228 t).
Proof. exact (EQ_MP (@lem5162292 t) (@lem5162267 t)). Qed.
Lemma lem5162294 (t : real -> Prop) : (term185 t) = (term185 t).
Proof. exact (eq_refl (term185 t)). Qed.
Lemma lem5162295 (t : real -> Prop) : (term187 t) = (term229 t).
Proof. exact (MK_COMB (@lem5162294 t) (@lem5162293 t)). Qed.
Lemma lem5162297 {A : Type'} (P : Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5162298 (P : Prop) (Q : type1028) : (term232 P Q) = (term233 P Q).
Proof. exact (@lem5162297 (real -> real) P Q). Qed.
Lemma lem5162299 (t : real -> Prop) : (term234 t) = (term235 t).
Proof. exact (@lem5162298 (term66 t) (term227 t)). Qed.
Lemma lem5162300 (t : real -> Prop) (x : real -> real) : (term236 t x) = (term225 t x).
Proof. exact (eq_refl (term236 t x)). Qed.
Lemma lem5162301 (t : real -> Prop) : (term237 t) = (term227 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162300 t x)). Qed.
Lemma lem5162302 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162303 (t : real -> Prop) : (term238 t) = (term228 t).
Proof. exact (MK_COMB (@lem5162302) (@lem5162301 t)). Qed.
Lemma lem5162304 (t : real -> Prop) : (term185 t) = (term185 t).
Proof. exact (eq_refl (term185 t)). Qed.
Lemma lem5162305 (t : real -> Prop) : (term234 t) = (term229 t).
Proof. exact (MK_COMB (@lem5162304 t) (@lem5162303 t)). Qed.
Lemma lem5162306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5162307 (t : real -> Prop) : (term239 t) = (term240 t).
Proof. exact (MK_COMB (@lem5162306) (@lem5162305 t)). Qed.
Lemma lem5162308 (t : real -> Prop) (x : real -> real) : (term236 t x) = (term225 t x).
Proof. exact (eq_refl (term236 t x)). Qed.
Lemma lem5162309 (t : real -> Prop) : (term185 t) = (term185 t).
Proof. exact (eq_refl (term185 t)). Qed.
Lemma lem5162310 (t : real -> Prop) (x : real -> real) : (term241 t x) = (term242 t x).
Proof. exact (MK_COMB (@lem5162309 t) (@lem5162308 t x)). Qed.
Lemma lem5162311 (t : real -> Prop) : (term243 t) = (term244 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162310 t x)). Qed.
Lemma lem5162312 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162313 (t : real -> Prop) : (term235 t) = (term245 t).
Proof. exact (MK_COMB (@lem5162312) (@lem5162311 t)). Qed.
Lemma lem5162314 (t : real -> Prop) : ((term234 t) = (term235 t)) = ((term229 t) = (term245 t)).
Proof. exact (MK_COMB (@lem5162307 t) (@lem5162313 t)). Qed.
Lemma lem5162315 (t : real -> Prop) : (term229 t) = (term245 t).
Proof. exact (EQ_MP (@lem5162314 t) (@lem5162299 t)). Qed.
Lemma lem5162316 (t : real -> Prop) : (term187 t) = (term245 t).
Proof. exact (TRANS (@lem5162295 t) (@lem5162315 t)). Qed.
Lemma lem5162317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162318 (t : real -> Prop) : (term201 t) = (term246 t).
Proof. exact (MK_COMB (@lem5162317) (@lem5162316 t)). Qed.
Lemma lem5162320 {A : Type'} (P : A -> Prop) (Q : Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5162321 (P : real -> Prop) (Q : Prop) : (term249 P Q) = (term250 P Q).
Proof. exact (@lem5162320 real P Q). Qed.
Lemma lem5162322 (t : real -> Prop) (b : real) : (term251 t b) = (term252 t b).
Proof. exact (@lem5162321 (term174 t b) (term6 t b)). Qed.
Lemma lem5162323 (t : real -> Prop) (x : real) (b : real) : (term213 t b x) = (term168 t x b).
Proof. exact (eq_refl (term213 t b x)). Qed.
Lemma lem5162324 (t : real -> Prop) (b : real) : (term253 t b) = (term174 t b).
Proof. exact (fun_ext (fun x : real => @lem5162323 t x b)). Qed.
Lemma lem5162325 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162326 (t : real -> Prop) (b : real) : (term254 t b) = (term175 t b).
Proof. exact (MK_COMB (@lem5162325) (@lem5162324 t b)). Qed.
Lemma lem5162327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162328 (t : real -> Prop) (b : real) : (term255 t b) = (term193 t b).
Proof. exact (MK_COMB (@lem5162327) (@lem5162326 t b)). Qed.
Lemma lem5162329 (t : real -> Prop) (b : real) : (term6 t b) = (term6 t b).
Proof. exact (eq_refl (term6 t b)). Qed.
Lemma lem5162330 (t : real -> Prop) (b : real) : (term251 t b) = (term195 t b).
Proof. exact (MK_COMB (@lem5162328 t b) (@lem5162329 t b)). Qed.
Lemma lem5162331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5162332 (t : real -> Prop) (b : real) : (term256 t b) = (term257 t b).
Proof. exact (MK_COMB (@lem5162331) (@lem5162330 t b)). Qed.
Lemma lem5162333 (t : real -> Prop) (x : real) (b : real) : (term213 t b x) = (term168 t x b).
Proof. exact (eq_refl (term213 t b x)). Qed.
Lemma lem5162334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162335 (t : real -> Prop) (x : real) (b : real) : (term258 t b x) = (term259 t x b).
Proof. exact (MK_COMB (@lem5162334) (@lem5162333 t x b)). Qed.
Lemma lem5162336 (t : real -> Prop) (b : real) : (term6 t b) = (term6 t b).
Proof. exact (eq_refl (term6 t b)). Qed.
Lemma lem5162337 (x : real) (t : real -> Prop) (b : real) : (term260 x t b) = (term261 x t b).
Proof. exact (MK_COMB (@lem5162335 t x b) (@lem5162336 t b)). Qed.
Lemma lem5162338 (t : real -> Prop) (b : real) : (term262 t b) = (term263 t b).
Proof. exact (fun_ext (fun x : real => @lem5162337 x t b)). Qed.
Lemma lem5162339 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162340 (t : real -> Prop) (b : real) : (term252 t b) = (term264 t b).
Proof. exact (MK_COMB (@lem5162339) (@lem5162338 t b)). Qed.
Lemma lem5162341 (t : real -> Prop) (b : real) : ((term251 t b) = (term252 t b)) = ((term195 t b) = (term264 t b)).
Proof. exact (MK_COMB (@lem5162332 t b) (@lem5162340 t b)). Qed.
Lemma lem5162342 (t : real -> Prop) (b : real) : (term195 t b) = (term264 t b).
Proof. exact (EQ_MP (@lem5162341 t b) (@lem5162322 t b)). Qed.
Lemma lem5162343 (t : real -> Prop) : (term196 t) = (term265 t).
Proof. exact (fun_ext (fun b : real => @lem5162342 t b)). Qed.
Lemma lem5162344 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162345 (t : real -> Prop) : (term197 t) = (term266 t).
Proof. exact (MK_COMB (@lem5162344) (@lem5162343 t)). Qed.
Lemma lem5162347 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5162348 (P : type1626) : (term206 P) = (term207 P).
Proof. exact (@lem5162347 real real P). Qed.
Lemma lem5162349 (t : real -> Prop) : (term267 t) = (term268 t).
Proof. exact (@lem5162348 (term269 t)). Qed.
Lemma lem5162350 (t : real -> Prop) (b : real) : (term270 t b) = (term263 t b).
Proof. exact (eq_refl (term270 t b)). Qed.
Lemma lem5162351 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5162352 (t : real -> Prop) (b : real) (x : real) : (term271 t b x) = (term272 t b x).
Proof. exact (MK_COMB (@lem5162350 t b) (@lem5162351 x)). Qed.
Lemma lem5162353 (x : real) (t : real -> Prop) (b : real) : (term272 t b x) = (term261 x t b).
Proof. exact (eq_refl (term272 t b x)). Qed.
Lemma lem5162354 (x : real) (t : real -> Prop) (b : real) : (term271 t b x) = (term261 x t b).
Proof. exact (TRANS (@lem5162352 t b x) (@lem5162353 x t b)). Qed.
Lemma lem5162355 (t : real -> Prop) (b : real) : (term273 t b) = (term263 t b).
Proof. exact (fun_ext (fun x : real => @lem5162354 x t b)). Qed.
Lemma lem5162356 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162357 (t : real -> Prop) (b : real) : (term274 t b) = (term264 t b).
Proof. exact (MK_COMB (@lem5162356) (@lem5162355 t b)). Qed.
Lemma lem5162358 (t : real -> Prop) : (term275 t) = (term265 t).
Proof. exact (fun_ext (fun b : real => @lem5162357 t b)). Qed.
Lemma lem5162359 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162360 (t : real -> Prop) : (term267 t) = (term266 t).
Proof. exact (MK_COMB (@lem5162359) (@lem5162358 t)). Qed.
Lemma lem5162361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5162362 (t : real -> Prop) : (term276 t) = (term277 t).
Proof. exact (MK_COMB (@lem5162361) (@lem5162360 t)). Qed.
Lemma lem5162363 (t : real -> Prop) (b : real) : (term270 t b) = (term263 t b).
Proof. exact (eq_refl (term270 t b)). Qed.
Lemma lem5162364 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5162365 (t : real -> Prop) (x : real -> real) (b : real) : (term278 t x b) = (term279 t x b).
Proof. exact (MK_COMB (@lem5162363 t b) (@lem5162364 x b)). Qed.
Lemma lem5162366 (x : real -> real) (t : real -> Prop) (b : real) : (term279 t x b) = (term280 x t b).
Proof. exact (eq_refl (term279 t x b)). Qed.
Lemma lem5162367 (x : real -> real) (t : real -> Prop) (b : real) : (term278 t x b) = (term280 x t b).
Proof. exact (TRANS (@lem5162365 t x b) (@lem5162366 x t b)). Qed.
Lemma lem5162368 (x : real -> real) (t : real -> Prop) : (term281 t x) = (term282 x t).
Proof. exact (fun_ext (fun b : real => @lem5162367 x t b)). Qed.
Lemma lem5162369 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162370 (x : real -> real) (t : real -> Prop) : (term283 t x) = (term284 x t).
Proof. exact (MK_COMB (@lem5162369) (@lem5162368 x t)). Qed.
Lemma lem5162371 (t : real -> Prop) : (term285 t) = (term286 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162370 x t)). Qed.
Lemma lem5162372 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162373 (t : real -> Prop) : (term268 t) = (term287 t).
Proof. exact (MK_COMB (@lem5162372) (@lem5162371 t)). Qed.
Lemma lem5162374 (t : real -> Prop) : ((term267 t) = (term268 t)) = ((term266 t) = (term287 t)).
Proof. exact (MK_COMB (@lem5162362 t) (@lem5162373 t)). Qed.
Lemma lem5162375 (t : real -> Prop) : (term266 t) = (term287 t).
Proof. exact (EQ_MP (@lem5162374 t) (@lem5162349 t)). Qed.
Lemma lem5162376 (t : real -> Prop) : (term197 t) = (term287 t).
Proof. exact (TRANS (@lem5162345 t) (@lem5162375 t)). Qed.
Lemma lem5162377 (t : real -> Prop) : (term198 t) = (term198 t).
Proof. exact (eq_refl (term198 t)). Qed.
Lemma lem5162378 (t : real -> Prop) : (term199 t) = (term288 t).
Proof. exact (MK_COMB (@lem5162377 t) (@lem5162376 t)). Qed.
Lemma lem5162380 {A : Type'} (P : Prop) (Q : A -> Prop) : (term146 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5162381 (P : Prop) (Q : type1028) : (term289 P Q) = (term290 P Q).
Proof. exact (@lem5162380 (real -> real) P Q). Qed.
Lemma lem5162382 (t : real -> Prop) : (term291 t) = (term292 t).
Proof. exact (@lem5162381 (term191 t) (term286 t)). Qed.
Lemma lem5162383 (x : real -> real) (t : real -> Prop) : (term293 t x) = (term284 x t).
Proof. exact (eq_refl (term293 t x)). Qed.
Lemma lem5162384 (t : real -> Prop) : (term294 t) = (term286 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162383 x t)). Qed.
Lemma lem5162385 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162386 (t : real -> Prop) : (term295 t) = (term287 t).
Proof. exact (MK_COMB (@lem5162385) (@lem5162384 t)). Qed.
Lemma lem5162387 (t : real -> Prop) : (term198 t) = (term198 t).
Proof. exact (eq_refl (term198 t)). Qed.
Lemma lem5162388 (t : real -> Prop) : (term291 t) = (term288 t).
Proof. exact (MK_COMB (@lem5162387 t) (@lem5162386 t)). Qed.
Lemma lem5162389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5162390 (t : real -> Prop) : (term296 t) = (term297 t).
Proof. exact (MK_COMB (@lem5162389) (@lem5162388 t)). Qed.
Lemma lem5162391 (x : real -> real) (t : real -> Prop) : (term293 t x) = (term284 x t).
Proof. exact (eq_refl (term293 t x)). Qed.
Lemma lem5162392 (t : real -> Prop) : (term198 t) = (term198 t).
Proof. exact (eq_refl (term198 t)). Qed.
Lemma lem5162393 (x : real -> real) (t : real -> Prop) : (term298 t x) = (term299 x t).
Proof. exact (MK_COMB (@lem5162392 t) (@lem5162391 x t)). Qed.
Lemma lem5162394 (t : real -> Prop) : (term300 t) = (term301 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162393 x t)). Qed.
Lemma lem5162395 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162396 (t : real -> Prop) : (term292 t) = (term302 t).
Proof. exact (MK_COMB (@lem5162395) (@lem5162394 t)). Qed.
Lemma lem5162397 (t : real -> Prop) : ((term291 t) = (term292 t)) = ((term288 t) = (term302 t)).
Proof. exact (MK_COMB (@lem5162390 t) (@lem5162396 t)). Qed.
Lemma lem5162398 (t : real -> Prop) : (term288 t) = (term302 t).
Proof. exact (EQ_MP (@lem5162397 t) (@lem5162382 t)). Qed.
Lemma lem5162399 (t : real -> Prop) : (term199 t) = (term302 t).
Proof. exact (TRANS (@lem5162378 t) (@lem5162398 t)). Qed.
Lemma lem5162400 (t : real -> Prop) : (term203 t) = (term303 t).
Proof. exact (MK_COMB (@lem5162318 t) (@lem5162399 t)). Qed.
Lemma lem5162402 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5162403 (P : type1028) (Q : type1028) : (term306 P Q) = (term307 P Q).
Proof. exact (@lem5162402 (real -> real) P Q). Qed.
Lemma lem5162404 (t : real -> Prop) : (term308 t) = (term309 t).
Proof. exact (@lem5162403 (term244 t) (term301 t)). Qed.
Lemma lem5162405 (t : real -> Prop) (x : real -> real) : (term310 t x) = (term242 t x).
Proof. exact (eq_refl (term310 t x)). Qed.
Lemma lem5162406 (t : real -> Prop) : (term311 t) = (term244 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162405 t x)). Qed.
Lemma lem5162407 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162408 (t : real -> Prop) : (term312 t) = (term245 t).
Proof. exact (MK_COMB (@lem5162407) (@lem5162406 t)). Qed.
Lemma lem5162409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162410 (t : real -> Prop) : (term313 t) = (term246 t).
Proof. exact (MK_COMB (@lem5162409) (@lem5162408 t)). Qed.
Lemma lem5162411 (x : real -> real) (t : real -> Prop) : (term314 t x) = (term299 x t).
Proof. exact (eq_refl (term314 t x)). Qed.
Lemma lem5162412 (t : real -> Prop) : (term315 t) = (term301 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162411 x t)). Qed.
Lemma lem5162413 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162414 (t : real -> Prop) : (term316 t) = (term302 t).
Proof. exact (MK_COMB (@lem5162413) (@lem5162412 t)). Qed.
Lemma lem5162415 (t : real -> Prop) : (term308 t) = (term303 t).
Proof. exact (MK_COMB (@lem5162410 t) (@lem5162414 t)). Qed.
Lemma lem5162416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5162417 (t : real -> Prop) : (term317 t) = (term318 t).
Proof. exact (MK_COMB (@lem5162416) (@lem5162415 t)). Qed.
Lemma lem5162418 (t : real -> Prop) (x : real -> real) : (term310 t x) = (term242 t x).
Proof. exact (eq_refl (term310 t x)). Qed.
Lemma lem5162419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162420 (t : real -> Prop) (x : real -> real) : (term319 t x) = (term320 t x).
Proof. exact (MK_COMB (@lem5162419) (@lem5162418 t x)). Qed.
Lemma lem5162421 (x : real -> real) (t : real -> Prop) : (term314 t x) = (term299 x t).
Proof. exact (eq_refl (term314 t x)). Qed.
Lemma lem5162422 (x : real -> real) (t : real -> Prop) : (term321 t x) = (term322 x t).
Proof. exact (MK_COMB (@lem5162420 t x) (@lem5162421 x t)). Qed.
Lemma lem5162423 (t : real -> Prop) : (term323 t) = (term324 t).
Proof. exact (fun_ext (fun x : real -> real => @lem5162422 x t)). Qed.
Lemma lem5162424 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5162425 (t : real -> Prop) : (term309 t) = (term325 t).
Proof. exact (MK_COMB (@lem5162424) (@lem5162423 t)). Qed.
Lemma lem5162426 (t : real -> Prop) : ((term308 t) = (term309 t)) = ((term303 t) = (term325 t)).
Proof. exact (MK_COMB (@lem5162417 t) (@lem5162425 t)). Qed.
Lemma lem5162427 (t : real -> Prop) : (term303 t) = (term325 t).
Proof. exact (EQ_MP (@lem5162426 t) (@lem5162404 t)). Qed.
Lemma lem5162429 (t : real -> Prop) : (term203 t) = (term325 t).
Proof. exact (TRANS (@lem5162400 t) (@lem5162427 t)). Qed.
Lemma lem5162430 (t : real -> Prop) : (term95 t) = (term325 t).
Proof. exact (TRANS (@lem5162102 t) (@lem5162429 t)). Qed.
Lemma lem5162431 (t : real -> Prop) (h1 : term95 t) : term325 t.
Proof. exact (EQ_MP (@lem5162430 t) (@lem5161861 t h1)). Qed.
Lemma lem5162432 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5162433 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5162432 s x)). Qed.
Lemma lem5162434 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162435 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5162434) (@lem5162433 s)). Qed.
Lemma lem5162436 (s : real -> Prop) : (term166 s) = (term66 s).
Proof. exact (@lem16933 (term66 s)). Qed.
Lemma lem5162437 (s : real -> Prop) : (term166 s) = (term66 s).
Proof. exact (TRANS (@lem5162436 s) (@lem5162435 s)). Qed.
Lemma lem5162444 (s : real -> Prop) (x : real) (t : real -> Prop) : (term326 s x t) = (term327 s x t).
Proof. exact (@lem17362 (s x) (term77 x t)). Qed.
Lemma lem5162445 (P : real -> Prop) : (term134 P) = (term135 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5162446 (s : real -> Prop) (t : real -> Prop) : (term328 s t) = (term329 s t).
Proof. exact (@lem5162445 (term100 s t)). Qed.
Lemma lem5162447 (s : real -> Prop) (x : real) (t : real -> Prop) : (term330 s t x) = (term98 s x t).
Proof. exact (eq_refl (term330 s t x)). Qed.
Lemma lem5162448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5162449 (s : real -> Prop) (x : real) (t : real -> Prop) : (term331 s t x) = (term326 s x t).
Proof. exact (MK_COMB (@lem5162448) (@lem5162447 s x t)). Qed.
Lemma lem5162450 (s : real -> Prop) (x : real) (t : real -> Prop) : (term331 s t x) = (term327 s x t).
Proof. exact (TRANS (@lem5162449 s x t) (@lem5162444 s x t)). Qed.
Lemma lem5162451 (s : real -> Prop) (t : real -> Prop) : (term332 s t) = (term333 s t).
Proof. exact (fun_ext (fun x : real => @lem5162450 s x t)). Qed.
Lemma lem5162452 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162453 (s : real -> Prop) (t : real -> Prop) : (term329 s t) = (term334 s t).
Proof. exact (MK_COMB (@lem5162452) (@lem5162451 s t)). Qed.
Lemma lem5162454 (s : real -> Prop) (t : real -> Prop) : (term328 s t) = (term334 s t).
Proof. exact (TRANS (@lem5162446 s t) (@lem5162453 s t)). Qed.
Lemma lem5162455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162456 (s : real -> Prop) : (term184 s) = (term185 s).
Proof. exact (MK_COMB (@lem5162455) (@lem5162437 s)). Qed.
Lemma lem5162457 (s : real -> Prop) (t : real -> Prop) : (term335 s t) = (term336 s t).
Proof. exact (MK_COMB (@lem5162456 s) (@lem5162454 s t)). Qed.
Lemma lem5162458 (s : real -> Prop) (t : real -> Prop) : (term126 s t) = (term335 s t).
Proof. exact (@lem17045 (term67 s) (term101 s t)). Qed.
Lemma lem5162459 (s : real -> Prop) (t : real -> Prop) : (term126 s t) = (term336 s t).
Proof. exact (TRANS (@lem5162458 s t) (@lem5162457 s t)). Qed.
Lemma lem5162494 {A : Type'} (P : Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5162495 (P : Prop) (Q : real -> Prop) : (term337 P Q) = (term338 P Q).
Proof. exact (@lem5162494 real P Q). Qed.
Lemma lem5162496 (s : real -> Prop) (t : real -> Prop) : (term339 s t) = (term340 s t).
Proof. exact (@lem5162495 (term66 s) (term333 s t)). Qed.
Lemma lem5162497 (s : real -> Prop) (x : real) (t : real -> Prop) : (term341 s t x) = (term327 s x t).
Proof. exact (eq_refl (term341 s t x)). Qed.
Lemma lem5162498 (s : real -> Prop) (t : real -> Prop) : (term342 s t) = (term333 s t).
Proof. exact (fun_ext (fun x : real => @lem5162497 s x t)). Qed.
Lemma lem5162499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162500 (s : real -> Prop) (t : real -> Prop) : (term343 s t) = (term334 s t).
Proof. exact (MK_COMB (@lem5162499) (@lem5162498 s t)). Qed.
Lemma lem5162501 (s : real -> Prop) : (term185 s) = (term185 s).
Proof. exact (eq_refl (term185 s)). Qed.
Lemma lem5162502 (s : real -> Prop) (t : real -> Prop) : (term339 s t) = (term336 s t).
Proof. exact (MK_COMB (@lem5162501 s) (@lem5162500 s t)). Qed.
Lemma lem5162503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5162504 (s : real -> Prop) (t : real -> Prop) : (term344 s t) = (term345 s t).
Proof. exact (MK_COMB (@lem5162503) (@lem5162502 s t)). Qed.
Lemma lem5162505 (s : real -> Prop) (x : real) (t : real -> Prop) : (term341 s t x) = (term327 s x t).
Proof. exact (eq_refl (term341 s t x)). Qed.
Lemma lem5162506 (s : real -> Prop) : (term185 s) = (term185 s).
Proof. exact (eq_refl (term185 s)). Qed.
Lemma lem5162507 (s : real -> Prop) (x : real) (t : real -> Prop) : (term346 s t x) = (term347 s x t).
Proof. exact (MK_COMB (@lem5162506 s) (@lem5162505 s x t)). Qed.
Lemma lem5162508 (s : real -> Prop) (t : real -> Prop) : (term348 s t) = (term349 s t).
Proof. exact (fun_ext (fun x : real => @lem5162507 s x t)). Qed.
Lemma lem5162509 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5162510 (s : real -> Prop) (t : real -> Prop) : (term340 s t) = (term350 s t).
Proof. exact (MK_COMB (@lem5162509) (@lem5162508 s t)). Qed.
Lemma lem5162511 (s : real -> Prop) (t : real -> Prop) : ((term339 s t) = (term340 s t)) = ((term336 s t) = (term350 s t)).
Proof. exact (MK_COMB (@lem5162504 s t) (@lem5162510 s t)). Qed.
Lemma lem5162513 (s : real -> Prop) (t : real -> Prop) : (term336 s t) = (term350 s t).
Proof. exact (EQ_MP (@lem5162511 s t) (@lem5162496 s t)). Qed.
Lemma lem5162514 (s : real -> Prop) (t : real -> Prop) : (term126 s t) = (term350 s t).
Proof. exact (TRANS (@lem5162459 s t) (@lem5162513 s t)). Qed.
Lemma lem5162515 (s : real -> Prop) (t : real -> Prop) (h1 : term126 s t) : term350 s t.
Proof. exact (EQ_MP (@lem5162514 s t) (@lem5161866 s t h1)). Qed.
Lemma lem5162516 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term347 s x t) : term347 s x t.
Proof. exact (h1). Qed.
Lemma lem5162517 (x' : real -> real) (t : real -> Prop) (h1 : term322 x' t) : term322 x' t.
Proof. exact (h1). Qed.
Lemma lem5162518 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term162 b t s x''.
Proof. exact (h1). Qed.
Lemma lem5162533 (s : real -> Prop) (x : real) (t : real -> Prop) : (term327 s x t) = (term327 s x t).
Proof. exact (eq_refl (term327 s x t)). Qed.
Lemma lem5162538 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5162539 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5162538 s x)). Qed.
Lemma lem5162540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162541 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5162540) (@lem5162539 s)). Qed.
Lemma lem5162542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162543 (s : real -> Prop) : (term185 s) = (term185 s).
Proof. exact (MK_COMB (@lem5162542) (@lem5162541 s)). Qed.
Lemma lem5162544 (s : real -> Prop) (x : real) (t : real -> Prop) : (term347 s x t) = (term347 s x t).
Proof. exact (MK_COMB (@lem5162543 s) (@lem5162533 s x t)). Qed.
Lemma lem5162545 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term347 s x t) : term347 s x t.
Proof. exact (EQ_MP (@lem5162544 s x t) (@lem5162516 s x t h1)). Qed.
Lemma lem5162552 (t : real -> Prop) (b : real) : (term6 t b) = (term6 t b).
Proof. exact (eq_refl (term6 t b)). Qed.
Lemma lem5162561 (x' : real -> real) (b : real) : (term351 x' b) = (term351 x' b).
Proof. exact (eq_refl (term351 x' b)). Qed.
Lemma lem5162568 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5162569 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5162568 real Prop f x). Qed.
Lemma lem5162571 (t : real -> Prop) (x' : real -> real) (b : real) : (term352 t x' b) = (term353 t x' b).
Proof. exact (@lem5162569 t (x' b)). Qed.
Lemma lem5162572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5162573 (t : real -> Prop) (x' : real -> real) (b : real) : (term354 t x' b) = (term355 t x' b).
Proof. exact (MK_COMB (@lem5162572) (@lem5162571 t x' b)). Qed.
Lemma lem5162574 (t : real -> Prop) (x' : real -> real) (b : real) : (term221 t x' b) = (term356 t x' b).
Proof. exact (MK_COMB (@lem5162573 t x' b) (@lem5162561 x' b)). Qed.
Lemma lem5162575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162576 (t : real -> Prop) (x' : real -> real) (b : real) : (term357 t x' b) = (term358 t x' b).
Proof. exact (MK_COMB (@lem5162575) (@lem5162574 t x' b)). Qed.
Lemma lem5162577 (x' : real -> real) (t : real -> Prop) (b : real) : (term280 x' t b) = (term359 x' t b).
Proof. exact (MK_COMB (@lem5162576 t x' b) (@lem5162552 t b)). Qed.
Lemma lem5162578 (x' : real -> real) (t : real -> Prop) : (term282 x' t) = (term360 x' t).
Proof. exact (fun_ext (fun b : real => @lem5162577 x' t b)). Qed.
Lemma lem5162579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162580 (x' : real -> real) (t : real -> Prop) : (term284 x' t) = (term361 x' t).
Proof. exact (MK_COMB (@lem5162579) (@lem5162578 x' t)). Qed.
Lemma lem5162587 (x : real) (t : real -> Prop) : (term77 x t) = (term77 x t).
Proof. exact (eq_refl (term77 x t)). Qed.
Lemma lem5162588 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5162593 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5162594 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5162593 real Prop f x). Qed.
Lemma lem5162596 (t : real -> Prop) (x : real) : (t x) = (@I (real -> Prop) t x).
Proof. exact (@lem5162594 t x). Qed.
Lemma lem5162597 (t : real -> Prop) (x : real) : (term63 t x) = (term362 t x).
Proof. exact (MK_COMB (@lem5162588) (@lem5162596 t x)). Qed.
Lemma lem5162598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162599 (t : real -> Prop) (x : real) : (term363 t x) = (term364 t x).
Proof. exact (MK_COMB (@lem5162598) (@lem5162597 t x)). Qed.
Lemma lem5162600 (x : real) (t : real -> Prop) : (term189 x t) = (term365 x t).
Proof. exact (MK_COMB (@lem5162599 t x) (@lem5162587 x t)). Qed.
Lemma lem5162601 (t : real -> Prop) : (term190 t) = (term366 t).
Proof. exact (fun_ext (fun x : real => @lem5162600 x t)). Qed.
Lemma lem5162602 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162603 (t : real -> Prop) : (term191 t) = (term367 t).
Proof. exact (MK_COMB (@lem5162602) (@lem5162601 t)). Qed.
Lemma lem5162604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5162605 (t : real -> Prop) : (term198 t) = (term368 t).
Proof. exact (MK_COMB (@lem5162604) (@lem5162603 t)). Qed.
Lemma lem5162606 (x' : real -> real) (t : real -> Prop) : (term299 x' t) = (term369 x' t).
Proof. exact (MK_COMB (@lem5162605 t) (@lem5162580 x' t)). Qed.
Lemma lem5162615 (x' : real -> real) (b : real) : (term351 x' b) = (term351 x' b).
Proof. exact (eq_refl (term351 x' b)). Qed.
Lemma lem5162622 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5162623 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5162622 real Prop f x). Qed.
Lemma lem5162625 (t : real -> Prop) (x' : real -> real) (b : real) : (term352 t x' b) = (term353 t x' b).
Proof. exact (@lem5162623 t (x' b)). Qed.
Lemma lem5162626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5162627 (t : real -> Prop) (x' : real -> real) (b : real) : (term354 t x' b) = (term355 t x' b).
Proof. exact (MK_COMB (@lem5162626) (@lem5162625 t x' b)). Qed.
Lemma lem5162628 (t : real -> Prop) (x' : real -> real) (b : real) : (term221 t x' b) = (term356 t x' b).
Proof. exact (MK_COMB (@lem5162627 t x' b) (@lem5162615 x' b)). Qed.
Lemma lem5162629 (t : real -> Prop) (x' : real -> real) : (term223 t x') = (term370 t x').
Proof. exact (fun_ext (fun b : real => @lem5162628 t x' b)). Qed.
Lemma lem5162630 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162631 (t : real -> Prop) (x' : real -> real) : (term225 t x') = (term371 t x').
Proof. exact (MK_COMB (@lem5162630) (@lem5162629 t x')). Qed.
Lemma lem5162632 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5162637 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5162638 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5162637 real Prop f x). Qed.
Lemma lem5162640 (t : real -> Prop) (x : real) : (t x) = (@I (real -> Prop) t x).
Proof. exact (@lem5162638 t x). Qed.
Lemma lem5162641 (t : real -> Prop) (x : real) : (term63 t x) = (term362 t x).
Proof. exact (MK_COMB (@lem5162632) (@lem5162640 t x)). Qed.
Lemma lem5162642 (t : real -> Prop) : (term65 t) = (term372 t).
Proof. exact (fun_ext (fun x : real => @lem5162641 t x)). Qed.
Lemma lem5162643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162644 (t : real -> Prop) : (term66 t) = (term373 t).
Proof. exact (MK_COMB (@lem5162643) (@lem5162642 t)). Qed.
Lemma lem5162645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162646 (t : real -> Prop) : (term185 t) = (term374 t).
Proof. exact (MK_COMB (@lem5162645) (@lem5162644 t)). Qed.
Lemma lem5162647 (t : real -> Prop) (x' : real -> real) : (term242 t x') = (term375 t x').
Proof. exact (MK_COMB (@lem5162646 t) (@lem5162631 t x')). Qed.
Lemma lem5162648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162649 (t : real -> Prop) (x' : real -> real) : (term320 t x') = (term376 t x').
Proof. exact (MK_COMB (@lem5162648) (@lem5162647 t x')). Qed.
Lemma lem5162650 (x' : real -> real) (t : real -> Prop) : (term322 x' t) = (term377 x' t).
Proof. exact (MK_COMB (@lem5162649 t x') (@lem5162606 x' t)). Qed.
Lemma lem5162651 (x' : real -> real) (t : real -> Prop) (h1 : term322 x' t) : term377 x' t.
Proof. exact (EQ_MP (@lem5162650 x' t) (@lem5162517 x' t h1)). Qed.
Lemma lem5162654 (s : real -> Prop) (x'' : real) : (s x'') = (s x'').
Proof. exact (eq_refl (s x'')). Qed.
Lemma lem5162659 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5162660 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5162659 real Prop f x). Qed.
Lemma lem5162662 (t : real -> Prop) (x : real) : (t x) = (@I (real -> Prop) t x).
Proof. exact (@lem5162660 t x). Qed.
Lemma lem5162669 (s : real -> Prop) (x : real) : (term363 s x) = (term363 s x).
Proof. exact (eq_refl (term363 s x)). Qed.
Lemma lem5162670 (s : real -> Prop) (t : real -> Prop) (x : real) : (term130 s t x) = (term378 s t x).
Proof. exact (MK_COMB (@lem5162669 s x) (@lem5162662 t x)). Qed.
Lemma lem5162671 (s : real -> Prop) (t : real -> Prop) : (term131 s t) = (term379 s t).
Proof. exact (fun_ext (fun x : real => @lem5162670 s t x)). Qed.
Lemma lem5162672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162673 (s : real -> Prop) (t : real -> Prop) : (term132 s t) = (term380 s t).
Proof. exact (MK_COMB (@lem5162672) (@lem5162671 s t)). Qed.
Lemma lem5162674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5162675 (s : real -> Prop) (t : real -> Prop) : (term142 s t) = (term381 s t).
Proof. exact (MK_COMB (@lem5162674) (@lem5162673 s t)). Qed.
Lemma lem5162676 (t : real -> Prop) (s : real -> Prop) (x'' : real) : (term156 t s x'') = (term382 t s x'').
Proof. exact (MK_COMB (@lem5162675 s t) (@lem5162654 s x'')). Qed.
Lemma lem5162681 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5162682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5162687 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5162688 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem5162687 real Prop f x). Qed.
Lemma lem5162690 (t : real -> Prop) (x : real) : (t x) = (@I (real -> Prop) t x).
Proof. exact (@lem5162688 t x). Qed.
Lemma lem5162691 (t : real -> Prop) (x : real) : (term63 t x) = (term362 t x).
Proof. exact (MK_COMB (@lem5162682) (@lem5162690 t x)). Qed.
Lemma lem5162692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5162693 (t : real -> Prop) (x : real) : (term363 t x) = (term364 t x).
Proof. exact (MK_COMB (@lem5162692) (@lem5162691 t x)). Qed.
Lemma lem5162694 (t : real -> Prop) (x : real) (b : real) : (term127 t x b) = (term383 t x b).
Proof. exact (MK_COMB (@lem5162693 t x) (@lem5162681 x b)). Qed.
Lemma lem5162695 (t : real -> Prop) (b : real) : (term128 t b) = (term384 t b).
Proof. exact (fun_ext (fun x : real => @lem5162694 t x b)). Qed.
Lemma lem5162696 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162697 (t : real -> Prop) (b : real) : (term129 t b) = (term385 t b).
Proof. exact (MK_COMB (@lem5162696) (@lem5162695 t b)). Qed.
Lemma lem5162698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5162699 (t : real -> Prop) (b : real) : (term144 t b) = (term386 t b).
Proof. exact (MK_COMB (@lem5162698) (@lem5162697 t b)). Qed.
Lemma lem5162700 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) : (term162 b t s x'') = (term387 b t s x'').
Proof. exact (MK_COMB (@lem5162699 t b) (@lem5162676 t s x'')). Qed.
Lemma lem5162701 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term387 b t s x''.
Proof. exact (EQ_MP (@lem5162700 b t s x'') (@lem5162518 b t s x'' h1)). Qed.
Lemma lem5162702 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term382 t s x''.
Proof. exact (proj2 (@lem5162701 b t s x'' h1)). Qed.
Lemma lem5162703 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term385 t b.
Proof. exact (proj1 (@lem5162701 b t s x'' h1)). Qed.
Lemma lem5162705 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term380 s t.
Proof. exact (proj1 (@lem5162702 b t s x'' h1)). Qed.
Lemma lem5162706 (t : real -> Prop) (x' : real -> real) (h1 : term375 t x') : term375 t x'.
Proof. exact (h1). Qed.
Lemma lem5162707 (x' : real -> real) (t : real -> Prop) (h1 : term369 x' t) : term369 x' t.
Proof. exact (h1). Qed.
Lemma lem5162708 (t : real -> Prop) (h1 : term373 t) : term373 t.
Proof. exact (h1). Qed.
Lemma lem5162709 (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term371 t x'.
Proof. exact (h1). Qed.
Lemma lem5162710 (s : real -> Prop) (h1 : term66 s) : term66 s.
Proof. exact (h1). Qed.
Lemma lem5162711 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : term327 s x t.
Proof. exact (h1). Qed.
Lemma lem5162714 (s : real -> Prop) (h1 : term66 s) : term66 s.
Proof. exact (h1). Qed.
Lemma lem5162719 (x' : real -> real) (t : real -> Prop) (h1 : term369 x' t) : term367 t.
Proof. exact (proj1 (@lem5162707 x' t h1)). Qed.
Lemma lem5162720 (s : real -> Prop) (h1 : term66 s) : term66 s.
Proof. exact (h1). Qed.
Lemma lem5162721 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : term327 s x t.
Proof. exact (h1). Qed.
Lemma lem5162762 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5162763 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5162762 s x)). Qed.
Lemma lem5162764 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162766 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5162764) (@lem5162763 s)). Qed.
Lemma lem5162767 (s : real -> Prop) (h1 : term66 s) : term66 s.
Proof. exact (EQ_MP (@lem5162766 s) (@lem5162710 s h1)). Qed.
Lemma lem5162788 (s : real -> Prop) (t : real -> Prop) (x : real) : (term378 s t x) = (term378 s t x).
Proof. exact (eq_refl (term378 s t x)). Qed.
Lemma lem5162789 (s : real -> Prop) (t : real -> Prop) : (term379 s t) = (term379 s t).
Proof. exact (fun_ext (fun x : real => @lem5162788 s t x)). Qed.
Lemma lem5162790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162792 (s : real -> Prop) (t : real -> Prop) : (term380 s t) = (term380 s t).
Proof. exact (MK_COMB (@lem5162790) (@lem5162789 s t)). Qed.
Lemma lem5162793 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term380 s t.
Proof. exact (EQ_MP (@lem5162792 s t) (@lem5162705 b t s x'' h1)). Qed.
Lemma lem5162799 (t : real -> Prop) (x : real) : (term362 t x) = (term362 t x).
Proof. exact (eq_refl (term362 t x)). Qed.
Lemma lem5162800 (t : real -> Prop) : (term372 t) = (term372 t).
Proof. exact (fun_ext (fun x : real => @lem5162799 t x)). Qed.
Lemma lem5162801 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162803 (t : real -> Prop) : (term373 t) = (term373 t).
Proof. exact (MK_COMB (@lem5162801) (@lem5162800 t)). Qed.
Lemma lem5162804 (t : real -> Prop) (h1 : term373 t) : term373 t.
Proof. exact (EQ_MP (@lem5162803 t) (@lem5162708 t h1)). Qed.
Lemma lem5162855 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5162856 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5162855 s x)). Qed.
Lemma lem5162857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162859 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5162857) (@lem5162856 s)). Qed.
Lemma lem5162860 (s : real -> Prop) (h1 : term66 s) : term66 s.
Proof. exact (EQ_MP (@lem5162859 s) (@lem5162714 s h1)). Qed.
Lemma lem5162868 (t : real -> Prop) (x : real) (b : real) : (term383 t x b) = (term383 t x b).
Proof. exact (eq_refl (term383 t x b)). Qed.
Lemma lem5162869 (t : real -> Prop) (b : real) : (term384 t b) = (term384 t b).
Proof. exact (fun_ext (fun x : real => @lem5162868 t x b)). Qed.
Lemma lem5162870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162872 (t : real -> Prop) (b : real) : (term385 t b) = (term385 t b).
Proof. exact (MK_COMB (@lem5162870) (@lem5162869 t b)). Qed.
Lemma lem5162873 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term385 t b.
Proof. exact (EQ_MP (@lem5162872 t b) (@lem5162703 b t s x'' h1)). Qed.
Lemma lem5162896 (t : real -> Prop) (x' : real -> real) (b : real) : (term356 t x' b) = (term356 t x' b).
Proof. exact (eq_refl (term356 t x' b)). Qed.
Lemma lem5162897 (t : real -> Prop) (x' : real -> real) : (term370 t x') = (term370 t x').
Proof. exact (fun_ext (fun b : real => @lem5162896 t x' b)). Qed.
Lemma lem5162898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162900 (t : real -> Prop) (x' : real -> real) : (term371 t x') = (term371 t x').
Proof. exact (MK_COMB (@lem5162898) (@lem5162897 t x')). Qed.
Lemma lem5162901 (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term371 t x'.
Proof. exact (EQ_MP (@lem5162900 t x') (@lem5162709 t x' h1)). Qed.
Lemma lem5162977 (s : real -> Prop) (x : real) : (term63 s x) = (term63 s x).
Proof. exact (eq_refl (term63 s x)). Qed.
Lemma lem5162978 (s : real -> Prop) : (term65 s) = (term65 s).
Proof. exact (fun_ext (fun x : real => @lem5162977 s x)). Qed.
Lemma lem5162979 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5162981 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (MK_COMB (@lem5162979) (@lem5162978 s)). Qed.
Lemma lem5162982 (s : real -> Prop) (h1 : term66 s) : term66 s.
Proof. exact (EQ_MP (@lem5162981 s) (@lem5162720 s h1)). Qed.
Lemma lem5163003 (s : real -> Prop) (t : real -> Prop) (x : real) : (term378 s t x) = (term378 s t x).
Proof. exact (eq_refl (term378 s t x)). Qed.
Lemma lem5163004 (s : real -> Prop) (t : real -> Prop) : (term379 s t) = (term379 s t).
Proof. exact (fun_ext (fun x : real => @lem5163003 s t x)). Qed.
Lemma lem5163005 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5163007 (s : real -> Prop) (t : real -> Prop) : (term380 s t) = (term380 s t).
Proof. exact (MK_COMB (@lem5163005) (@lem5163004 s t)). Qed.
Lemma lem5163008 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term380 s t.
Proof. exact (EQ_MP (@lem5163007 s t) (@lem5162705 b t s x'' h1)). Qed.
Lemma lem5163020 (x : real) (t : real -> Prop) : (term365 x t) = (term365 x t).
Proof. exact (eq_refl (term365 x t)). Qed.
Lemma lem5163021 (t : real -> Prop) : (term366 t) = (term366 t).
Proof. exact (fun_ext (fun x : real => @lem5163020 x t)). Qed.
Lemma lem5163022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5163024 (t : real -> Prop) : (term367 t) = (term367 t).
Proof. exact (MK_COMB (@lem5163022) (@lem5163021 t)). Qed.
Lemma lem5163025 (x' : real -> real) (t : real -> Prop) (h1 : term369 x' t) : term367 t.
Proof. exact (EQ_MP (@lem5163024 t) (@lem5162719 x' t h1)). Qed.
Lemma lem5163066 (_67478 : real) (s : real -> Prop) (h1 : term66 s) : term137 s _67478.
Proof. exact (@lem5162767 s h1 _67478). Qed.
Lemma lem5163067 (s : real -> Prop) (_67478 : real) : (term137 s _67478) = (term63 s _67478).
Proof. exact (eq_refl (term137 s _67478)). Qed.
Lemma lem5163072 (_67480 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term388 s t _67480.
Proof. exact (@lem5162793 b t s x'' h1 _67480). Qed.
Lemma lem5163073 (s : real -> Prop) (t : real -> Prop) (_67480 : real) : (term388 s t _67480) = (term378 s t _67480).
Proof. exact (eq_refl (term388 s t _67480)). Qed.
Lemma lem5163075 (_67481 : real) (t : real -> Prop) (h1 : term373 t) : term389 t _67481.
Proof. exact (@lem5162804 t h1 _67481). Qed.
Lemma lem5163076 (t : real -> Prop) (_67481 : real) : (term389 t _67481) = (term362 t _67481).
Proof. exact (eq_refl (term389 t _67481)). Qed.
Lemma lem5163087 (_67485 : real) (s : real -> Prop) (h1 : term66 s) : term137 s _67485.
Proof. exact (@lem5162860 s h1 _67485). Qed.
Lemma lem5163088 (s : real -> Prop) (_67485 : real) : (term137 s _67485) = (term63 s _67485).
Proof. exact (eq_refl (term137 s _67485)). Qed.
Lemma lem5163090 (_67486 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term390 t b _67486.
Proof. exact (@lem5162873 b t s x'' h1 _67486). Qed.
Lemma lem5163091 (t : real -> Prop) (_67486 : real) (b : real) : (term390 t b _67486) = (term383 t _67486 b).
Proof. exact (eq_refl (term390 t b _67486)). Qed.
Lemma lem5163096 (_67488 : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term391 t x' _67488.
Proof. exact (@lem5162901 t x' h1 _67488). Qed.
Lemma lem5163097 (t : real -> Prop) (x' : real -> real) (_67488 : real) : (term391 t x' _67488) = (term356 t x' _67488).
Proof. exact (eq_refl (term391 t x' _67488)). Qed.
Lemma lem5163098 (_67488 : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term356 t x' _67488.
Proof. exact (EQ_MP (@lem5163097 t x' _67488) (@lem5163096 _67488 t x' h1)). Qed.
Lemma lem5163111 (_67493 : real) (s : real -> Prop) (h1 : term66 s) : term137 s _67493.
Proof. exact (@lem5162982 s h1 _67493). Qed.
Lemma lem5163112 (s : real -> Prop) (_67493 : real) : (term137 s _67493) = (term63 s _67493).
Proof. exact (eq_refl (term137 s _67493)). Qed.
Lemma lem5163117 (_67495 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term388 s t _67495.
Proof. exact (@lem5163008 b t s x'' h1 _67495). Qed.
Lemma lem5163118 (s : real -> Prop) (t : real -> Prop) (_67495 : real) : (term388 s t _67495) = (term378 s t _67495).
Proof. exact (eq_refl (term388 s t _67495)). Qed.
Lemma lem5163120 (_67496 : real) (x' : real -> real) (t : real -> Prop) (h1 : term369 x' t) : term392 t _67496.
Proof. exact (@lem5163025 x' t h1 _67496). Qed.
Lemma lem5163121 (_67496 : real) (t : real -> Prop) : (term392 t _67496) = (term365 _67496 t).
Proof. exact (eq_refl (term392 t _67496)). Qed.
Lemma lem5163151 (_67478 : real) (s : real -> Prop) (h1 : term66 s) : term63 s _67478.
Proof. exact (EQ_MP (@lem5163067 s _67478) (@lem5163066 _67478 s h1)). Qed.
Lemma lem5163163 (_67480 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term378 s t _67480.
Proof. exact (EQ_MP (@lem5163073 s t _67480) (@lem5163072 _67480 b t s x'' h1)). Qed.
Lemma lem5163167 (_67481 : real) (t : real -> Prop) (h1 : term373 t) : term362 t _67481.
Proof. exact (EQ_MP (@lem5163076 t _67481) (@lem5163075 _67481 t h1)). Qed.
Lemma lem5163187 (_67485 : real) (s : real -> Prop) (h1 : term66 s) : term63 s _67485.
Proof. exact (EQ_MP (@lem5163088 s _67485) (@lem5163087 _67485 s h1)). Qed.
Lemma lem5163197 (_67486 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term383 t _67486 b.
Proof. exact (EQ_MP (@lem5163091 t _67486 b) (@lem5163090 _67486 b t s x'' h1)). Qed.
Lemma lem5163213 (_67488 : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term351 x' _67488.
Proof. exact (proj2 (@lem5163098 _67488 t x' h1)). Qed.
Lemma lem5163235 (_67493 : real) (s : real -> Prop) (h1 : term66 s) : term63 s _67493.
Proof. exact (EQ_MP (@lem5163112 s _67493) (@lem5163111 _67493 s h1)). Qed.
Lemma lem5163259 (_67495 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term378 s t _67495.
Proof. exact (EQ_MP (@lem5163118 s t _67495) (@lem5163117 _67495 b t s x'' h1)). Qed.
Lemma lem5163267 (_67496 : real) (x' : real -> real) (t : real -> Prop) (h1 : term369 x' t) : term365 _67496 t.
Proof. exact (EQ_MP (@lem5163121 _67496 t) (@lem5163120 _67496 x' t h1)). Qed.
Lemma lem5163271 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : term393 x t.
Proof. exact (proj2 (@lem5162721 s x t h1)). Qed.
Lemma lem5163285 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : s x''.
Proof. exact (proj2 (@lem5162702 b t s x'' h1)). Qed.
Lemma lem5163286 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term394 s x''.
Proof. exact (fun h0 : term63 s x'' => @lem5163285 b t s x'' h1). Qed.
Lemma lem5163288 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163289 (s : real -> Prop) (x'' : real) : (term394 s x'') = (s x'').
Proof. exact (@lem5163288 (s x'')). Qed.
Lemma lem5163290 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : s x''.
Proof. exact (EQ_MP (@lem5163289 s x'') (@lem5163286 b t s x'' h1)). Qed.
Lemma lem5163293 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5163295 (s : real -> Prop) (_67478 : real) : (term63 s _67478) = (term396 s _67478).
Proof. exact (@lem5163293 (s _67478)). Qed.
Lemma lem5163298 (_67478 : real) (s : real -> Prop) (h1 : term66 s) : term396 s _67478.
Proof. exact (EQ_MP (@lem5163295 s _67478) (@lem5163151 _67478 s h1)). Qed.
Lemma lem5163299 (x'' : real) (s : real -> Prop) (h1 : term66 s) : term396 s x''.
Proof. exact (@lem5163298 x'' s h1). Qed.
Lemma lem5163302 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (@lem5163299 x'' s h1 (@lem5163290 b t s x'' h2)). Qed.
Lemma lem5163303 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : term397.
Proof. exact (fun h0 : ~ False => @lem5163302 b t s x'' h1 h2). Qed.
Lemma lem5163305 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163306 : term397 = False.
Proof. exact (@lem5163305 False). Qed.
Lemma lem5163307 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (EQ_MP (@lem5163306) (@lem5163303 b t s x'' h1 h2)). Qed.
Lemma lem5163309 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : s x.
Proof. exact (proj1 (@lem5162711 s x t h1)). Qed.
Lemma lem5163310 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : term394 s x.
Proof. exact (fun h0 : term63 s x => @lem5163309 s x t h1). Qed.
Lemma lem5163312 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163313 (s : real -> Prop) (x : real) : (term394 s x) = (s x).
Proof. exact (@lem5163312 (s x)). Qed.
Lemma lem5163314 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : s x.
Proof. exact (EQ_MP (@lem5163313 s x) (@lem5163310 s x t h1)). Qed.
Lemma lem5163320 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5163321 (t : real -> Prop) (s : real -> Prop) (_67480 : real) : (term378 s t _67480) = (term398 t s _67480).
Proof. exact (@lem5163320 (@I (real -> Prop) t _67480) (term63 s _67480)). Qed.
Lemma lem5163327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5163328 (t : real -> Prop) (s : real -> Prop) (_67480 : real) : (term399 s t _67480) = (term400 t s _67480).
Proof. exact (MK_COMB (@lem5163327) (@lem5163321 t s _67480)). Qed.
Lemma lem5163334 (t : real -> Prop) (s : real -> Prop) (_67480 : real) : (term398 t s _67480) = (term398 t s _67480).
Proof. exact (eq_refl (term398 t s _67480)). Qed.
Lemma lem5163335 (t : real -> Prop) (s : real -> Prop) (_67480 : real) : ((term378 s t _67480) = (term398 t s _67480)) = ((term398 t s _67480) = (term398 t s _67480)).
Proof. exact (MK_COMB (@lem5163328 t s _67480) (@lem5163334 t s _67480)). Qed.
Lemma lem5163337 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5163338 (x : Prop) : (x = x) = True.
Proof. exact (@lem5163337 Prop x). Qed.
Lemma lem5163339 (t : real -> Prop) (s : real -> Prop) (_67480 : real) : ((term398 t s _67480) = (term398 t s _67480)) = True.
Proof. exact (@lem5163338 (term398 t s _67480)). Qed.
Lemma lem5163340 (t : real -> Prop) (s : real -> Prop) (_67480 : real) : ((term378 s t _67480) = (term398 t s _67480)) = True.
Proof. exact (TRANS (@lem5163335 t s _67480) (@lem5163339 t s _67480)). Qed.
Lemma lem5163341 (t : real -> Prop) (s : real -> Prop) (_67480 : real) : True = ((term378 s t _67480) = (term398 t s _67480)).
Proof. exact (SYM (@lem5163340 t s _67480)). Qed.
Lemma lem5163342 (t : real -> Prop) (s : real -> Prop) (_67480 : real) : (term378 s t _67480) = (term398 t s _67480).
Proof. exact (EQ_MP (@lem5163341 t s _67480) (@lem0)). Qed.
Lemma lem5163343 (_67480 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term398 t s _67480.
Proof. exact (EQ_MP (@lem5163342 t s _67480) (@lem5163163 _67480 b t s x'' h1)). Qed.
Lemma lem5163345 (b : Prop) (a : Prop) : (a \/ b) = (term401 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5163346 (s : real -> Prop) (t : real -> Prop) (_67480 : real) : (term398 t s _67480) = (term402 s t _67480).
Proof. exact (@lem5163345 (term63 s _67480) (@I (real -> Prop) t _67480)). Qed.
Lemma lem5163348 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5163349 (s : real -> Prop) (_67480 : real) : (term133 s _67480) = (s _67480).
Proof. exact (@lem5163348 (s _67480)). Qed.
Lemma lem5163350 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5163351 (s : real -> Prop) (_67480 : real) : (term403 s _67480) = (term48 s _67480).
Proof. exact (MK_COMB (@lem5163350) (@lem5163349 s _67480)). Qed.
Lemma lem5163352 (t : real -> Prop) (_67480 : real) : (@I (real -> Prop) t _67480) = (@I (real -> Prop) t _67480).
Proof. exact (eq_refl (@I (real -> Prop) t _67480)). Qed.
Lemma lem5163353 (s : real -> Prop) (t : real -> Prop) (_67480 : real) : (term402 s t _67480) = (term404 s t _67480).
Proof. exact (MK_COMB (@lem5163351 s _67480) (@lem5163352 t _67480)). Qed.
Lemma lem5163354 (s : real -> Prop) (t : real -> Prop) (_67480 : real) : (term398 t s _67480) = (term404 s t _67480).
Proof. exact (TRANS (@lem5163346 s t _67480) (@lem5163353 s t _67480)). Qed.
Lemma lem5163357 (_67480 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term404 s t _67480.
Proof. exact (EQ_MP (@lem5163354 s t _67480) (@lem5163343 _67480 b t s x'' h1)). Qed.
Lemma lem5163358 (x : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term404 s t x.
Proof. exact (@lem5163357 x b t s x'' h1). Qed.
Lemma lem5163361 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term327 s x t) : @I (real -> Prop) t x.
Proof. exact (@lem5163358 x b t s x'' h1 (@lem5163314 s x t h2)). Qed.
Lemma lem5163362 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term327 s x t) : term405 t x.
Proof. exact (fun h0 : term362 t x => @lem5163361 b x'' s x t h1 h2). Qed.
Lemma lem5163364 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163365 (t : real -> Prop) (x : real) : (term405 t x) = (@I (real -> Prop) t x).
Proof. exact (@lem5163364 (@I (real -> Prop) t x)). Qed.
Lemma lem5163366 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term327 s x t) : @I (real -> Prop) t x.
Proof. exact (EQ_MP (@lem5163365 t x) (@lem5163362 b x'' s x t h1 h2)). Qed.
Lemma lem5163369 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5163371 (t : real -> Prop) (_67481 : real) : (term362 t _67481) = (term406 t _67481).
Proof. exact (@lem5163369 (@I (real -> Prop) t _67481)). Qed.
Lemma lem5163374 (_67481 : real) (t : real -> Prop) (h1 : term373 t) : term406 t _67481.
Proof. exact (EQ_MP (@lem5163371 t _67481) (@lem5163167 _67481 t h1)). Qed.
Lemma lem5163375 (x : real) (t : real -> Prop) (h1 : term373 t) : term406 t x.
Proof. exact (@lem5163374 x t h1). Qed.
Lemma lem5163378 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term373 t) (h2 : term162 b t s x'') (h3 : term327 s x t) : False.
Proof. exact (@lem5163375 x t h1 (@lem5163366 b x'' s x t h2 h3)). Qed.
Lemma lem5163379 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term373 t) (h2 : term162 b t s x'') (h3 : term327 s x t) : term397.
Proof. exact (fun h0 : ~ False => @lem5163378 b x'' s x t h1 h2 h3). Qed.
Lemma lem5163381 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163382 : term397 = False.
Proof. exact (@lem5163381 False). Qed.
Lemma lem5163383 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term373 t) (h2 : term162 b t s x'') (h3 : term327 s x t) : False.
Proof. exact (EQ_MP (@lem5163382) (@lem5163379 b x'' s x t h1 h2 h3)). Qed.
Lemma lem5163385 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : s x''.
Proof. exact (proj2 (@lem5162702 b t s x'' h1)). Qed.
Lemma lem5163386 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term394 s x''.
Proof. exact (fun h0 : term63 s x'' => @lem5163385 b t s x'' h1). Qed.
Lemma lem5163388 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163389 (s : real -> Prop) (x'' : real) : (term394 s x'') = (s x'').
Proof. exact (@lem5163388 (s x'')). Qed.
Lemma lem5163390 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : s x''.
Proof. exact (EQ_MP (@lem5163389 s x'') (@lem5163386 b t s x'' h1)). Qed.
Lemma lem5163393 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5163395 (s : real -> Prop) (_67485 : real) : (term63 s _67485) = (term396 s _67485).
Proof. exact (@lem5163393 (s _67485)). Qed.
Lemma lem5163398 (_67485 : real) (s : real -> Prop) (h1 : term66 s) : term396 s _67485.
Proof. exact (EQ_MP (@lem5163395 s _67485) (@lem5163187 _67485 s h1)). Qed.
Lemma lem5163399 (x'' : real) (s : real -> Prop) (h1 : term66 s) : term396 s x''.
Proof. exact (@lem5163398 x'' s h1). Qed.
Lemma lem5163402 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (@lem5163399 x'' s h1 (@lem5163390 b t s x'' h2)). Qed.
Lemma lem5163403 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : term397.
Proof. exact (fun h0 : ~ False => @lem5163402 b t s x'' h1 h2). Qed.
Lemma lem5163405 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163406 : term397 = False.
Proof. exact (@lem5163405 False). Qed.
Lemma lem5163407 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (EQ_MP (@lem5163406) (@lem5163403 b t s x'' h1 h2)). Qed.
Lemma lem5163409 (_67488 : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term353 t x' _67488.
Proof. exact (proj1 (@lem5163098 _67488 t x' h1)). Qed.
Lemma lem5163410 (b : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term353 t x' b.
Proof. exact (@lem5163409 b t x' h1). Qed.
Lemma lem5163411 (b : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term407 t x' b.
Proof. exact (fun h0 : term408 t x' b => @lem5163410 b t x' h1). Qed.
Lemma lem5163413 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163414 (t : real -> Prop) (x' : real -> real) (b : real) : (term407 t x' b) = (term353 t x' b).
Proof. exact (@lem5163413 (term353 t x' b)). Qed.
Lemma lem5163415 (b : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term353 t x' b.
Proof. exact (EQ_MP (@lem5163414 t x' b) (@lem5163411 b t x' h1)). Qed.
Lemma lem5163421 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5163422 (b : real) (t : real -> Prop) (_67486 : real) : (term383 t _67486 b) = (term409 b t _67486).
Proof. exact (@lem5163421 (real_le _67486 b) (term362 t _67486)). Qed.
Lemma lem5163428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5163429 (b : real) (t : real -> Prop) (_67486 : real) : (term410 t _67486 b) = (term411 b t _67486).
Proof. exact (MK_COMB (@lem5163428) (@lem5163422 b t _67486)). Qed.
Lemma lem5163435 (b : real) (t : real -> Prop) (_67486 : real) : (term409 b t _67486) = (term409 b t _67486).
Proof. exact (eq_refl (term409 b t _67486)). Qed.
Lemma lem5163436 (b : real) (t : real -> Prop) (_67486 : real) : ((term383 t _67486 b) = (term409 b t _67486)) = ((term409 b t _67486) = (term409 b t _67486)).
Proof. exact (MK_COMB (@lem5163429 b t _67486) (@lem5163435 b t _67486)). Qed.
Lemma lem5163438 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5163439 (x : Prop) : (x = x) = True.
Proof. exact (@lem5163438 Prop x). Qed.
Lemma lem5163440 (b : real) (t : real -> Prop) (_67486 : real) : ((term409 b t _67486) = (term409 b t _67486)) = True.
Proof. exact (@lem5163439 (term409 b t _67486)). Qed.
Lemma lem5163441 (b : real) (t : real -> Prop) (_67486 : real) : ((term383 t _67486 b) = (term409 b t _67486)) = True.
Proof. exact (TRANS (@lem5163436 b t _67486) (@lem5163440 b t _67486)). Qed.
Lemma lem5163442 (b : real) (t : real -> Prop) (_67486 : real) : True = ((term383 t _67486 b) = (term409 b t _67486)).
Proof. exact (SYM (@lem5163441 b t _67486)). Qed.
Lemma lem5163443 (b : real) (t : real -> Prop) (_67486 : real) : (term383 t _67486 b) = (term409 b t _67486).
Proof. exact (EQ_MP (@lem5163442 b t _67486) (@lem0)). Qed.
Lemma lem5163444 (_67486 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term409 b t _67486.
Proof. exact (EQ_MP (@lem5163443 b t _67486) (@lem5163197 _67486 b t s x'' h1)). Qed.
Lemma lem5163446 (b : Prop) (a : Prop) : (a \/ b) = (term401 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5163447 (t : real -> Prop) (_67486 : real) (b : real) : (term409 b t _67486) = (term412 t _67486 b).
Proof. exact (@lem5163446 (term362 t _67486) (real_le _67486 b)). Qed.
Lemma lem5163449 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5163450 (t : real -> Prop) (_67486 : real) : (term413 t _67486) = (@I (real -> Prop) t _67486).
Proof. exact (@lem5163449 (@I (real -> Prop) t _67486)). Qed.
Lemma lem5163451 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5163452 (t : real -> Prop) (_67486 : real) : (term414 t _67486) = (term415 t _67486).
Proof. exact (MK_COMB (@lem5163451) (@lem5163450 t _67486)). Qed.
Lemma lem5163453 (_67486 : real) (b : real) : (real_le _67486 b) = (real_le _67486 b).
Proof. exact (eq_refl (real_le _67486 b)). Qed.
Lemma lem5163454 (t : real -> Prop) (_67486 : real) (b : real) : (term412 t _67486 b) = (term416 t _67486 b).
Proof. exact (MK_COMB (@lem5163452 t _67486) (@lem5163453 _67486 b)). Qed.
Lemma lem5163455 (t : real -> Prop) (_67486 : real) (b : real) : (term409 b t _67486) = (term416 t _67486 b).
Proof. exact (TRANS (@lem5163447 t _67486 b) (@lem5163454 t _67486 b)). Qed.
Lemma lem5163458 (_67486 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term416 t _67486 b.
Proof. exact (EQ_MP (@lem5163455 t _67486 b) (@lem5163444 _67486 b t s x'' h1)). Qed.
Lemma lem5163459 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term417 t x' b.
Proof. exact (@lem5163458 (x' b) b t s x'' h1). Qed.
Lemma lem5163462 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term371 t x') (h2 : term162 b t s x'') : term418 x' b.
Proof. exact (@lem5163459 x' b t s x'' h2 (@lem5163415 b t x' h1)). Qed.
Lemma lem5163463 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term371 t x') (h2 : term162 b t s x'') : term419 x' b.
Proof. exact (fun h0 : term351 x' b => @lem5163462 x' b t s x'' h1 h2). Qed.
Lemma lem5163465 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163466 (x' : real -> real) (b : real) : (term419 x' b) = (term418 x' b).
Proof. exact (@lem5163465 (term418 x' b)). Qed.
Lemma lem5163467 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term371 t x') (h2 : term162 b t s x'') : term418 x' b.
Proof. exact (EQ_MP (@lem5163466 x' b) (@lem5163463 x' b t s x'' h1 h2)). Qed.
Lemma lem5163470 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5163472 (x' : real -> real) (_67488 : real) : (term351 x' _67488) = (term420 x' _67488).
Proof. exact (@lem5163470 (term418 x' _67488)). Qed.
Lemma lem5163475 (_67488 : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term420 x' _67488.
Proof. exact (EQ_MP (@lem5163472 x' _67488) (@lem5163213 _67488 t x' h1)). Qed.
Lemma lem5163476 (b : real) (t : real -> Prop) (x' : real -> real) (h1 : term371 t x') : term420 x' b.
Proof. exact (@lem5163475 b t x' h1). Qed.
Lemma lem5163479 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term371 t x') (h2 : term162 b t s x'') : False.
Proof. exact (@lem5163476 b t x' h1 (@lem5163467 x' b t s x'' h1 h2)). Qed.
Lemma lem5163480 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term371 t x') (h2 : term162 b t s x'') : term397.
Proof. exact (fun h0 : ~ False => @lem5163479 x' b t s x'' h1 h2). Qed.
Lemma lem5163482 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163483 : term397 = False.
Proof. exact (@lem5163482 False). Qed.
Lemma lem5163484 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term371 t x') (h2 : term162 b t s x'') : False.
Proof. exact (EQ_MP (@lem5163483) (@lem5163480 x' b t s x'' h1 h2)). Qed.
Lemma lem5163486 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : s x''.
Proof. exact (proj2 (@lem5162702 b t s x'' h1)). Qed.
Lemma lem5163487 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term394 s x''.
Proof. exact (fun h0 : term63 s x'' => @lem5163486 b t s x'' h1). Qed.
Lemma lem5163489 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163490 (s : real -> Prop) (x'' : real) : (term394 s x'') = (s x'').
Proof. exact (@lem5163489 (s x'')). Qed.
Lemma lem5163491 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : s x''.
Proof. exact (EQ_MP (@lem5163490 s x'') (@lem5163487 b t s x'' h1)). Qed.
Lemma lem5163494 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5163496 (s : real -> Prop) (_67493 : real) : (term63 s _67493) = (term396 s _67493).
Proof. exact (@lem5163494 (s _67493)). Qed.
Lemma lem5163499 (_67493 : real) (s : real -> Prop) (h1 : term66 s) : term396 s _67493.
Proof. exact (EQ_MP (@lem5163496 s _67493) (@lem5163235 _67493 s h1)). Qed.
Lemma lem5163500 (x'' : real) (s : real -> Prop) (h1 : term66 s) : term396 s x''.
Proof. exact (@lem5163499 x'' s h1). Qed.
Lemma lem5163503 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (@lem5163500 x'' s h1 (@lem5163491 b t s x'' h2)). Qed.
Lemma lem5163504 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : term397.
Proof. exact (fun h0 : ~ False => @lem5163503 b t s x'' h1 h2). Qed.
Lemma lem5163506 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163507 : term397 = False.
Proof. exact (@lem5163506 False). Qed.
Lemma lem5163508 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (EQ_MP (@lem5163507) (@lem5163504 b t s x'' h1 h2)). Qed.
Lemma lem5163510 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : s x.
Proof. exact (proj1 (@lem5162721 s x t h1)). Qed.
Lemma lem5163511 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : term394 s x.
Proof. exact (fun h0 : term63 s x => @lem5163510 s x t h1). Qed.
Lemma lem5163513 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163514 (s : real -> Prop) (x : real) : (term394 s x) = (s x).
Proof. exact (@lem5163513 (s x)). Qed.
Lemma lem5163515 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : s x.
Proof. exact (EQ_MP (@lem5163514 s x) (@lem5163511 s x t h1)). Qed.
Lemma lem5163521 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5163522 (t : real -> Prop) (s : real -> Prop) (_67495 : real) : (term378 s t _67495) = (term398 t s _67495).
Proof. exact (@lem5163521 (@I (real -> Prop) t _67495) (term63 s _67495)). Qed.
Lemma lem5163528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5163529 (t : real -> Prop) (s : real -> Prop) (_67495 : real) : (term399 s t _67495) = (term400 t s _67495).
Proof. exact (MK_COMB (@lem5163528) (@lem5163522 t s _67495)). Qed.
Lemma lem5163535 (t : real -> Prop) (s : real -> Prop) (_67495 : real) : (term398 t s _67495) = (term398 t s _67495).
Proof. exact (eq_refl (term398 t s _67495)). Qed.
Lemma lem5163536 (t : real -> Prop) (s : real -> Prop) (_67495 : real) : ((term378 s t _67495) = (term398 t s _67495)) = ((term398 t s _67495) = (term398 t s _67495)).
Proof. exact (MK_COMB (@lem5163529 t s _67495) (@lem5163535 t s _67495)). Qed.
Lemma lem5163538 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5163539 (x : Prop) : (x = x) = True.
Proof. exact (@lem5163538 Prop x). Qed.
Lemma lem5163540 (t : real -> Prop) (s : real -> Prop) (_67495 : real) : ((term398 t s _67495) = (term398 t s _67495)) = True.
Proof. exact (@lem5163539 (term398 t s _67495)). Qed.
Lemma lem5163541 (t : real -> Prop) (s : real -> Prop) (_67495 : real) : ((term378 s t _67495) = (term398 t s _67495)) = True.
Proof. exact (TRANS (@lem5163536 t s _67495) (@lem5163540 t s _67495)). Qed.
Lemma lem5163542 (t : real -> Prop) (s : real -> Prop) (_67495 : real) : True = ((term378 s t _67495) = (term398 t s _67495)).
Proof. exact (SYM (@lem5163541 t s _67495)). Qed.
Lemma lem5163543 (t : real -> Prop) (s : real -> Prop) (_67495 : real) : (term378 s t _67495) = (term398 t s _67495).
Proof. exact (EQ_MP (@lem5163542 t s _67495) (@lem0)). Qed.
Lemma lem5163544 (_67495 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term398 t s _67495.
Proof. exact (EQ_MP (@lem5163543 t s _67495) (@lem5163259 _67495 b t s x'' h1)). Qed.
Lemma lem5163546 (b : Prop) (a : Prop) : (a \/ b) = (term401 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5163547 (s : real -> Prop) (t : real -> Prop) (_67495 : real) : (term398 t s _67495) = (term402 s t _67495).
Proof. exact (@lem5163546 (term63 s _67495) (@I (real -> Prop) t _67495)). Qed.
Lemma lem5163549 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5163550 (s : real -> Prop) (_67495 : real) : (term133 s _67495) = (s _67495).
Proof. exact (@lem5163549 (s _67495)). Qed.
Lemma lem5163551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5163552 (s : real -> Prop) (_67495 : real) : (term403 s _67495) = (term48 s _67495).
Proof. exact (MK_COMB (@lem5163551) (@lem5163550 s _67495)). Qed.
Lemma lem5163553 (t : real -> Prop) (_67495 : real) : (@I (real -> Prop) t _67495) = (@I (real -> Prop) t _67495).
Proof. exact (eq_refl (@I (real -> Prop) t _67495)). Qed.
Lemma lem5163554 (s : real -> Prop) (t : real -> Prop) (_67495 : real) : (term402 s t _67495) = (term404 s t _67495).
Proof. exact (MK_COMB (@lem5163552 s _67495) (@lem5163553 t _67495)). Qed.
Lemma lem5163555 (s : real -> Prop) (t : real -> Prop) (_67495 : real) : (term398 t s _67495) = (term404 s t _67495).
Proof. exact (TRANS (@lem5163547 s t _67495) (@lem5163554 s t _67495)). Qed.
Lemma lem5163558 (_67495 : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term404 s t _67495.
Proof. exact (EQ_MP (@lem5163555 s t _67495) (@lem5163544 _67495 b t s x'' h1)). Qed.
Lemma lem5163559 (x : real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term162 b t s x'') : term404 s t x.
Proof. exact (@lem5163558 x b t s x'' h1). Qed.
Lemma lem5163562 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term327 s x t) : @I (real -> Prop) t x.
Proof. exact (@lem5163559 x b t s x'' h1 (@lem5163515 s x t h2)). Qed.
Lemma lem5163563 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term327 s x t) : term405 t x.
Proof. exact (fun h0 : term362 t x => @lem5163562 b x'' s x t h1 h2). Qed.
Lemma lem5163565 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163566 (t : real -> Prop) (x : real) : (term405 t x) = (@I (real -> Prop) t x).
Proof. exact (@lem5163565 (@I (real -> Prop) t x)). Qed.
Lemma lem5163567 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term327 s x t) : @I (real -> Prop) t x.
Proof. exact (EQ_MP (@lem5163566 t x) (@lem5163563 b x'' s x t h1 h2)). Qed.
Lemma lem5163573 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5163574 (t : real -> Prop) (_67496 : real) : (term365 _67496 t) = (term421 t _67496).
Proof. exact (@lem5163573 (term77 _67496 t) (term362 t _67496)). Qed.
Lemma lem5163580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5163581 (t : real -> Prop) (_67496 : real) : (term422 _67496 t) = (term423 t _67496).
Proof. exact (MK_COMB (@lem5163580) (@lem5163574 t _67496)). Qed.
Lemma lem5163587 (t : real -> Prop) (_67496 : real) : (term421 t _67496) = (term421 t _67496).
Proof. exact (eq_refl (term421 t _67496)). Qed.
Lemma lem5163588 (t : real -> Prop) (_67496 : real) : ((term365 _67496 t) = (term421 t _67496)) = ((term421 t _67496) = (term421 t _67496)).
Proof. exact (MK_COMB (@lem5163581 t _67496) (@lem5163587 t _67496)). Qed.
Lemma lem5163590 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5163591 (x : Prop) : (x = x) = True.
Proof. exact (@lem5163590 Prop x). Qed.
Lemma lem5163592 (t : real -> Prop) (_67496 : real) : ((term421 t _67496) = (term421 t _67496)) = True.
Proof. exact (@lem5163591 (term421 t _67496)). Qed.
Lemma lem5163593 (t : real -> Prop) (_67496 : real) : ((term365 _67496 t) = (term421 t _67496)) = True.
Proof. exact (TRANS (@lem5163588 t _67496) (@lem5163592 t _67496)). Qed.
Lemma lem5163594 (t : real -> Prop) (_67496 : real) : True = ((term365 _67496 t) = (term421 t _67496)).
Proof. exact (SYM (@lem5163593 t _67496)). Qed.
Lemma lem5163595 (t : real -> Prop) (_67496 : real) : (term365 _67496 t) = (term421 t _67496).
Proof. exact (EQ_MP (@lem5163594 t _67496) (@lem0)). Qed.
Lemma lem5163596 (_67496 : real) (x' : real -> real) (t : real -> Prop) (h1 : term369 x' t) : term421 t _67496.
Proof. exact (EQ_MP (@lem5163595 t _67496) (@lem5163267 _67496 x' t h1)). Qed.
Lemma lem5163598 (b : Prop) (a : Prop) : (a \/ b) = (term401 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5163599 (_67496 : real) (t : real -> Prop) : (term421 t _67496) = (term424 _67496 t).
Proof. exact (@lem5163598 (term362 t _67496) (term77 _67496 t)). Qed.
Lemma lem5163601 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5163602 (t : real -> Prop) (_67496 : real) : (term413 t _67496) = (@I (real -> Prop) t _67496).
Proof. exact (@lem5163601 (@I (real -> Prop) t _67496)). Qed.
Lemma lem5163603 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5163604 (t : real -> Prop) (_67496 : real) : (term414 t _67496) = (term415 t _67496).
Proof. exact (MK_COMB (@lem5163603) (@lem5163602 t _67496)). Qed.
Lemma lem5163605 (_67496 : real) (t : real -> Prop) : (term77 _67496 t) = (term77 _67496 t).
Proof. exact (eq_refl (term77 _67496 t)). Qed.
Lemma lem5163606 (_67496 : real) (t : real -> Prop) : (term424 _67496 t) = (term425 _67496 t).
Proof. exact (MK_COMB (@lem5163604 t _67496) (@lem5163605 _67496 t)). Qed.
Lemma lem5163607 (_67496 : real) (t : real -> Prop) : (term421 t _67496) = (term425 _67496 t).
Proof. exact (TRANS (@lem5163599 _67496 t) (@lem5163606 _67496 t)). Qed.
Lemma lem5163610 (_67496 : real) (x' : real -> real) (t : real -> Prop) (h1 : term369 x' t) : term425 _67496 t.
Proof. exact (EQ_MP (@lem5163607 _67496 t) (@lem5163596 _67496 x' t h1)). Qed.
Lemma lem5163611 (x : real) (x' : real -> real) (t : real -> Prop) (h1 : term369 x' t) : term425 x t.
Proof. exact (@lem5163610 x x' t h1). Qed.
Lemma lem5163614 (b : real) (x'' : real) (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term369 x' t) (h3 : term327 s x t) : term77 x t.
Proof. exact (@lem5163611 x x' t h2 (@lem5163567 b x'' s x t h1 h3)). Qed.
Lemma lem5163615 (b : real) (x'' : real) (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term369 x' t) (h3 : term327 s x t) : term426 x t.
Proof. exact (fun h0 : term393 x t => @lem5163614 b x'' x' s x t h1 h2 h3). Qed.
Lemma lem5163617 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163618 (x : real) (t : real -> Prop) : (term426 x t) = (term77 x t).
Proof. exact (@lem5163617 (term77 x t)). Qed.
Lemma lem5163619 (b : real) (x'' : real) (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term369 x' t) (h3 : term327 s x t) : term77 x t.
Proof. exact (EQ_MP (@lem5163618 x t) (@lem5163615 b x'' x' s x t h1 h2 h3)). Qed.
Lemma lem5163622 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5163624 (x : real) (t : real -> Prop) : (term393 x t) = (term427 x t).
Proof. exact (@lem5163622 (term77 x t)). Qed.
Lemma lem5163627 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term327 s x t) : term427 x t.
Proof. exact (EQ_MP (@lem5163624 x t) (@lem5163271 s x t h1)). Qed.
Lemma lem5163630 (b : real) (x'' : real) (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term369 x' t) (h3 : term327 s x t) : False.
Proof. exact (@lem5163627 s x t h3 (@lem5163619 b x'' x' s x t h1 h2 h3)). Qed.
Lemma lem5163631 (b : real) (x'' : real) (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term369 x' t) (h3 : term327 s x t) : term397.
Proof. exact (fun h0 : ~ False => @lem5163630 b x'' x' s x t h1 h2 h3). Qed.
Lemma lem5163633 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5163634 : term397 = False.
Proof. exact (@lem5163633 False). Qed.
Lemma lem5163635 (b : real) (x'' : real) (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term369 x' t) (h3 : term327 s x t) : False.
Proof. exact (EQ_MP (@lem5163634) (@lem5163631 b x'' x' s x t h1 h2 h3)). Qed.
Lemma lem5163636 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : (term66 s) = False.
Proof. exact (prop_ext (fun h3 : term66 s => @lem5163508 b t s x'' h1 h2) (fun h3 : False => @lem5162982 s h1)). Qed.
Lemma lem5163637 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (EQ_MP (@lem5163636 b t s x'' h1 h2) (@lem5162982 s h1)). Qed.
Lemma lem5163638 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term371 t x') (h2 : term162 b t s x'') : (term371 t x') = False.
Proof. exact (prop_ext (fun h3 : term371 t x' => @lem5163484 x' b t s x'' h1 h2) (fun h3 : False => @lem5162901 t x' h1)). Qed.
Lemma lem5163639 (x' : real -> real) (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term371 t x') (h2 : term162 b t s x'') : False.
Proof. exact (EQ_MP (@lem5163638 x' b t s x'' h1 h2) (@lem5162901 t x' h1)). Qed.
Lemma lem5163640 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : (term66 s) = False.
Proof. exact (prop_ext (fun h3 : term66 s => @lem5163407 b t s x'' h1 h2) (fun h3 : False => @lem5162860 s h1)). Qed.
Lemma lem5163641 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (EQ_MP (@lem5163640 b t s x'' h1 h2) (@lem5162860 s h1)). Qed.
Lemma lem5163642 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term373 t) (h2 : term162 b t s x'') (h3 : term327 s x t) : (term373 t) = False.
Proof. exact (prop_ext (fun h4 : term373 t => @lem5163383 b x'' s x t h1 h2 h3) (fun h4 : False => @lem5162804 t h1)). Qed.
Lemma lem5163643 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term373 t) (h2 : term162 b t s x'') (h3 : term327 s x t) : False.
Proof. exact (EQ_MP (@lem5163642 b x'' s x t h1 h2 h3) (@lem5162804 t h1)). Qed.
Lemma lem5163644 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : (term66 s) = False.
Proof. exact (prop_ext (fun h3 : term66 s => @lem5163307 b t s x'' h1 h2) (fun h3 : False => @lem5162767 s h1)). Qed.
Lemma lem5163645 (b : real) (t : real -> Prop) (s : real -> Prop) (x'' : real) (h1 : term66 s) (h2 : term162 b t s x'') : False.
Proof. exact (EQ_MP (@lem5163644 b t s x'' h1 h2) (@lem5162767 s h1)). Qed.
Lemma lem5163646 (b : real) (x'' : real) (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term369 x' t) (h3 : term347 s x t) : False.
Proof. exact (or_elim (@lem5162545 s x t h3) (fun h0 : term66 s => @lem5163637 b t s x'' h0 h1) (fun h0 : term327 s x t => @lem5163635 b x'' x' s x t h1 h2 h0)). Qed.
Lemma lem5163647 (x' : real -> real) (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term371 t x') (h2 : term162 b t s x'') (h3 : term347 s x t) : False.
Proof. exact (or_elim (@lem5162545 s x t h3) (fun h0 : term66 s => @lem5163641 b t s x'' h0 h2) (fun h0 : term327 s x t => @lem5163639 x' b t s x'' h1 h2)). Qed.
Lemma lem5163648 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term373 t) (h2 : term162 b t s x'') (h3 : term347 s x t) : False.
Proof. exact (or_elim (@lem5162545 s x t h3) (fun h0 : term66 s => @lem5163645 b t s x'' h0 h2) (fun h0 : term327 s x t => @lem5163643 b x'' s x t h1 h2 h0)). Qed.
Lemma lem5163649 (b : real) (x'' : real) (s : real -> Prop) (x : real) (t : real -> Prop) (x' : real -> real) (h1 : term162 b t s x'') (h2 : term347 s x t) (h3 : term375 t x') : False.
Proof. exact (or_elim (@lem5162706 t x' h3) (fun h0 : term373 t => @lem5163648 b x'' s x t h0 h1 h2) (fun h0 : term371 t x' => @lem5163647 x' b x'' s x t h0 h1 h2)). Qed.
Lemma lem5163650 (b : real) (x'' : real) (s : real -> Prop) (x : real) (x' : real -> real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term347 s x t) (h3 : term322 x' t) : False.
Proof. exact (or_elim (@lem5162651 x' t h3) (fun h0 : term375 t x' => @lem5163649 b x'' s x t x' h1 h2 h0) (fun h0 : term369 x' t => @lem5163646 b x'' x' s x t h1 h0 h2)). Qed.
Lemma lem5163651 (b : real) (x'' : real) (s : real -> Prop) (x : real) (x' : real -> real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term347 s x t) (h3 : term322 x' t) : (term347 s x t) = False.
Proof. exact (prop_ext (fun h4 : term347 s x t => @lem5163650 b x'' s x x' t h1 h2 h3) (fun h4 : False => @lem5162545 s x t h2)). Qed.
Lemma lem5163652 (b : real) (x'' : real) (s : real -> Prop) (x : real) (x' : real -> real) (t : real -> Prop) (h1 : term162 b t s x'') (h2 : term347 s x t) (h3 : term322 x' t) : False.
Proof. exact (EQ_MP (@lem5163651 b x'' s x x' t h1 h2 h3) (@lem5162545 s x t h2)). Qed.
Lemma lem5163653 (b : real) (s : real -> Prop) (x : real) (x' : real -> real) (t : real -> Prop) (h1 : term69 b t s) (h2 : term347 s x t) (h3 : term322 x' t) : False.
Proof. exact (ex_elim (@lem5162020 b t s h1) (fun x'' : real => fun h0 : term164 b t s x'' => @lem5163652 b x'' s x x' t h0 h2 h3)). Qed.
Lemma lem5163654 (b : real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term69 b t s) (h2 : term95 t) (h3 : term347 s x t) : False.
Proof. exact (ex_elim (@lem5162431 t h2) (fun x' : real -> real => fun h0 : term324 t x' => @lem5163653 b s x x' t h1 h3 h0)). Qed.
Lemma lem5163655 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term126 s t) (h2 : term69 b t s) (h3 : term95 t) : False.
Proof. exact (ex_elim (@lem5162515 s t h1) (fun x : real => fun h0 : term349 s t x => @lem5163654 b s x t h2 h3 h0)). Qed.
Lemma lem5163656 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term126 s t) (h2 : term69 b t s) (h3 : term95 t) : (term126 s t) = False.
Proof. exact (prop_ext (fun h4 : term126 s t => @lem5163655 b s t h1 h2 h3) (fun h4 : False => @lem5161866 s t h1)). Qed.
Lemma lem5163657 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term126 s t) (h2 : term69 b t s) (h3 : term95 t) : False.
Proof. exact (EQ_MP (@lem5163656 b s t h1 h2 h3) (@lem5161866 s t h1)). Qed.
Lemma lem5163658 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term69 b t s) (h2 : term95 t) : term125 s t.
Proof. exact (fun h0 : term126 s t => @lem5163657 b s t h0 h1 h2). Qed.
Lemma lem5163659 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term69 b t s) (h2 : term95 t) : term102 s t.
Proof. exact (EQ_MP (@lem5161865 s t) (@lem5163658 b s t h1 h2)). Qed.
Lemma lem5163660 (b : real) (t : real -> Prop) (s : real -> Prop) (h1 : term69 b t s) : term103 s t.
Proof. exact (fun h0 : term95 t => @lem5163659 b s t h1 h0). Qed.
Lemma lem5163661 (b : real) (s : real -> Prop) (t : real -> Prop) : term104 b s t.
Proof. exact (fun h0 : term69 b t s => @lem5163660 b t s h0). Qed.
Lemma lem5163666 (s : real -> Prop) (t : real -> Prop) : term116 s t.
Proof. exact (fun b : real => @lem5163661 b s t). Qed.
Lemma lem5163671 (t : real -> Prop) : term120 t.
Proof. exact (fun s : real -> Prop => @lem5163666 s t). Qed.
Lemma lem5163676 : term124.
Proof. exact (fun t : real -> Prop => @lem5163671 t). Qed.
Lemma lem5163677 : term123.
Proof. exact (EQ_MP (@lem5161859) (@lem5163676)). Qed.
Lemma lem5163678 (t : real -> Prop) : term428 t.
Proof. exact (@lem5163677 t). Qed.
Lemma lem5163679 (t : real -> Prop) : (term428 t) = (term119 t).
Proof. exact (eq_refl (term428 t)). Qed.
Lemma lem5163680 (t : real -> Prop) : term119 t.
Proof. exact (EQ_MP (@lem5163679 t) (@lem5163678 t)). Qed.
Lemma lem5163681 (t : real -> Prop) (s : real -> Prop) : term429 t s.
Proof. exact (@lem5163680 t s). Qed.
Lemma lem5163682 (s : real -> Prop) (t : real -> Prop) : (term429 t s) = (term115 s t).
Proof. exact (eq_refl (term429 t s)). Qed.
Lemma lem5163683 (s : real -> Prop) (t : real -> Prop) : term115 s t.
Proof. exact (EQ_MP (@lem5163682 s t) (@lem5163681 t s)). Qed.
Lemma lem5163684 (s : real -> Prop) (t : real -> Prop) (b : real) : term430 s t b.
Proof. exact (@lem5163683 s t b). Qed.
Lemma lem5163685 (b : real) (s : real -> Prop) (t : real -> Prop) : (term430 s t b) = (term106 b s t).
Proof. exact (eq_refl (term430 s t b)). Qed.
Lemma lem5163686 (b : real) (s : real -> Prop) (t : real -> Prop) : term106 b s t.
Proof. exact (EQ_MP (@lem5163685 b s t) (@lem5163684 s t b)). Qed.
Lemma lem5163688 (b : real) (s : real -> Prop) (t : real -> Prop) : term106 b s t.
Proof. exact (@lem5161508 b s t (@lem5163686 b s t)). Qed.
Lemma lem5163689 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term107 b s t) : False.
Proof. exact (@lem5163688 b s t (@lem5161493 b s t h1)). Qed.
Lemma lem5163690 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term107 b s t) : (term107 b s t) = False.
Proof. exact (prop_ext (fun h2 : term107 b s t => @lem5163689 b s t h1) (fun h2 : False => @lem5161493 b s t h1)). Qed.
Lemma lem5163691 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term107 b s t) : False.
Proof. exact (EQ_MP (@lem5163690 b s t h1) (@lem5161493 b s t h1)). Qed.
Lemma lem5163692 (b : real) (s : real -> Prop) (t : real -> Prop) : term106 b s t.
Proof. exact (fun h0 : term107 b s t => @lem5163691 b s t h0). Qed.
Lemma lem5163693 (b : real) (s : real -> Prop) (t : real -> Prop) : term104 b s t.
Proof. exact (EQ_MP (@lem5161492 b s t) (@lem5163692 b s t)). Qed.
Lemma lem5163694 (b : real) (s : real -> Prop) (t : real -> Prop) : term46 b s t.
Proof. exact (EQ_MP (@lem5161488 b s t) (@lem5163693 b s t)). Qed.
Lemma lem5163695 (b : real) (s : real -> Prop) (t : real -> Prop) : term45 b s t.
Proof. exact (EQ_MP (@lem5161173 b s t) (@lem5163694 b s t)). Qed.
Lemma lem5163696 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 t b) (h2 : term11 s) (h3 : @SUBSET real s t) : term43 s t.
Proof. exact (@lem5163695 b s t (@lem5161022 b s t h1 h2 h3)). Qed.
Lemma lem5163697 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 t b) (h2 : term11 s) (h3 : @SUBSET real s t) : term41 s t.
Proof. exact (@lem5163696 b s t h1 h2 h3 (@lem5160985 t)). Qed.
Lemma lem5163698 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 t b) (h2 : term11 s) (h3 : @SUBSET real s t) : term431 s t.
Proof. exact (@lem5161010 s t (@lem5163697 b s t h1 h2 h3)). Qed.
Lemma lem5163699 (s : real -> Prop) (t : real -> Prop) (h1 : term9 s t) : term10 s t.
Proof. exact (proj2 (@lem5161002 s t h1)). Qed.
Lemma lem5163700 (s : real -> Prop) (t : real -> Prop) (h1 : term9 s t) : term11 s.
Proof. exact (proj1 (@lem5161002 s t h1)). Qed.
Lemma lem5163701 (s : real -> Prop) (t : real -> Prop) (h1 : term10 s t) : term12 t.
Proof. exact (proj2 (@lem5161003 s t h1)). Qed.
Lemma lem5163702 (s : real -> Prop) (t : real -> Prop) (h1 : term10 s t) : @SUBSET real s t.
Proof. exact (proj1 (@lem5161003 s t h1)). Qed.
Lemma lem5163703 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 t b) (h2 : term11 s) (h3 : @SUBSET real s t) : (term13 t b) = (term431 s t).
Proof. exact (prop_ext (fun h4 : term13 t b => @lem5163698 b s t h1 h2 h3) (fun h4 : term431 s t => @lem5161007 t b h1)). Qed.
Lemma lem5163704 (b : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 t b) (h2 : term11 s) (h3 : @SUBSET real s t) : term431 s t.
Proof. exact (EQ_MP (@lem5163703 b s t h1 h2 h3) (@lem5161007 t b h1)). Qed.
Lemma lem5163705 (s : real -> Prop) (t : real -> Prop) (h1 : term12 t) (h2 : term11 s) (h3 : @SUBSET real s t) : term431 s t.
Proof. exact (ex_elim (@lem5161005 t h1) (fun b : real => fun h0 : term72 t b => @lem5163704 b s t h0 h2 h3)). Qed.
Lemma lem5163706 (s : real -> Prop) (t : real -> Prop) (h1 : term12 t) (h2 : term11 s) (h3 : @SUBSET real s t) : (@SUBSET real s t) = (term431 s t).
Proof. exact (prop_ext (fun h4 : @SUBSET real s t => @lem5163705 s t h1 h2 h3) (fun h4 : term431 s t => @lem5161006 s t h3)). Qed.
Lemma lem5163707 (s : real -> Prop) (t : real -> Prop) (h1 : term12 t) (h2 : term11 s) (h3 : @SUBSET real s t) : term431 s t.
Proof. exact (EQ_MP (@lem5163706 s t h1 h2 h3) (@lem5161006 s t h3)). Qed.
Lemma lem5163708 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : term10 s t) (h3 : @SUBSET real s t) : (term12 t) = (term431 s t).
Proof. exact (prop_ext (fun h4 : term12 t => @lem5163707 s t h4 h1 h3) (fun h4 : term431 s t => @lem5163701 s t h2)). Qed.
Lemma lem5163709 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : term10 s t) (h3 : @SUBSET real s t) : term431 s t.
Proof. exact (EQ_MP (@lem5163708 s t h1 h2 h3) (@lem5163701 s t h2)). Qed.
Lemma lem5163710 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : term10 s t) : (@SUBSET real s t) = (term431 s t).
Proof. exact (prop_ext (fun h3 : @SUBSET real s t => @lem5163709 s t h1 h2 h3) (fun h3 : term431 s t => @lem5163702 s t h2)). Qed.
Lemma lem5163711 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : term10 s t) : term431 s t.
Proof. exact (EQ_MP (@lem5163710 s t h1 h2) (@lem5163702 s t h2)). Qed.
Lemma lem5163712 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : term10 s t) : (term11 s) = (term431 s t).
Proof. exact (prop_ext (fun h3 : term11 s => @lem5163711 s t h1 h2) (fun h3 : term431 s t => @lem5161004 s h1)). Qed.
Lemma lem5163713 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : term10 s t) : term431 s t.
Proof. exact (EQ_MP (@lem5163712 s t h1 h2) (@lem5161004 s h1)). Qed.
Lemma lem5163714 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : term9 s t) : (term10 s t) = (term431 s t).
Proof. exact (prop_ext (fun h3 : term10 s t => @lem5163713 s t h1 h3) (fun h3 : term431 s t => @lem5163699 s t h2)). Qed.
Lemma lem5163715 (s : real -> Prop) (t : real -> Prop) (h1 : term11 s) (h2 : term9 s t) : term431 s t.
Proof. exact (EQ_MP (@lem5163714 s t h1 h2) (@lem5163699 s t h2)). Qed.
Lemma lem5163716 (s : real -> Prop) (t : real -> Prop) (h1 : term9 s t) : (term11 s) = (term431 s t).
Proof. exact (prop_ext (fun h2 : term11 s => @lem5163715 s t h2 h1) (fun h2 : term431 s t => @lem5163700 s t h1)). Qed.
Lemma lem5163717 (s : real -> Prop) (t : real -> Prop) (h1 : term9 s t) : term431 s t.
Proof. exact (EQ_MP (@lem5163716 s t h1) (@lem5163700 s t h1)). Qed.
Lemma lem5163718 (s : real -> Prop) (t : real -> Prop) : term432 s t.
Proof. exact (fun h0 : term9 s t => @lem5163717 s t h0). Qed.
Lemma lem5163723 (s : real -> Prop) : term433 s.
Proof. exact (fun t : real -> Prop => @lem5163718 s t). Qed.
Lemma lem5163728 : term434.
Proof. exact (fun s : real -> Prop => @lem5163723 s). Qed.
