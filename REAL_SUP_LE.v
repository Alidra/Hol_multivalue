Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
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
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem5158931 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5158932 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5158933 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5158932 t1) (@lem5158931 t1)). Qed.
Lemma lem5158934 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5158933 t1 t2). Qed.
Lemma lem5158935 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5158936 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5158935 t1 t2) (@lem5158934 t1 t2)). Qed.
Lemma lem5158937 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5158936 t1 t2 t3). Qed.
Lemma lem5158938 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5158939 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5158938 t1 t2 t3) (@lem5158937 t1 t2 t3)). Qed.
Lemma lem5158940 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5158939 t1 t2 t3)). Qed.
Lemma lem5158942 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5158943 (s : real -> Prop) : (term8 s) = (term9 s).
Proof. exact (@lem5158942 (term8 s)). Qed.
Lemma lem5158944 (s : real -> Prop) : (term9 s) = (term8 s).
Proof. exact (SYM (@lem5158943 s)). Qed.
Lemma lem5158945 (s : real -> Prop) (h1 : term10 s) : term10 s.
Proof. exact (h1). Qed.
Lemma lem5158948 (s : real -> Prop) (h1 : term11 s) : term11 s.
Proof. exact (h1). Qed.
Lemma lem5158949 (s : real -> Prop) : term12 s.
Proof. exact (fun h0 : term11 s => @lem5158948 s h0). Qed.
Lemma lem5158950 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem5158951 (s : real -> Prop) (h1 : term11 s) : term11 s.
Proof. exact (h1). Qed.
Lemma lem5158952 (s : real -> Prop) (h1 : term11 s) (h2 : term12 s) : term11 s.
Proof. exact (@lem5158950 s h2 (@lem5158951 s h1)). Qed.
Lemma lem5158953 (s : real -> Prop) (h1 : term11 s) : term13 s.
Proof. exact (fun h0 : term12 s => @lem5158952 s h1 h0). Qed.
Lemma lem5158954 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem5158955 (s : real -> Prop) (h1 : term11 s) (h2 : term12 s) : term11 s.
Proof. exact (@lem5158953 s h1 (@lem5158954 s h2)). Qed.
Lemma lem5158956 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (fun h0 : term11 s => @lem5158955 s h0 h1). Qed.
Lemma lem5158957 (s : real -> Prop) : term14 s.
Proof. exact (fun h0 : term12 s => @lem5158956 s h0). Qed.
Lemma lem5158960 (s : real -> Prop) : term12 s.
Proof. exact (@lem5158957 s (@lem5158949 s)). Qed.
Lemma lem5158982 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5158983 : term15 = term16.
Proof. exact (@lem5158982 term17). Qed.
Lemma lem5159022 (s : real -> Prop) : (term18 s) = (term18 s).
Proof. exact (eq_refl (term18 s)). Qed.
Lemma lem5159023 (s : real -> Prop) : (term11 s) = (term19 s).
Proof. exact (MK_COMB (@lem5159022 s) (@lem5158983)). Qed.
Lemma lem5159026 : term20 = term21.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5159023 s)). Qed.
Lemma lem5159027 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5159036 : term22 = term23.
Proof. exact (MK_COMB (@lem5159027) (@lem5159026)). Qed.
Lemma lem5159037 (s : real -> Prop) (b : real) : (term24 s b) = (term24 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5159042 (s : real -> Prop) (x : real) (b : real) : (term25 s x b) = (term25 s x b).
Proof. exact (eq_refl (term25 s x b)). Qed.
Lemma lem5159043 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (fun_ext (fun x : real => @lem5159042 s x b)). Qed.
Lemma lem5159044 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159045 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (MK_COMB (@lem5159044) (@lem5159043 s b)). Qed.
Lemma lem5159046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5159047 (s : real -> Prop) (b : real) : (term28 s b) = (term28 s b).
Proof. exact (MK_COMB (@lem5159046) (@lem5159045 s b)). Qed.
Lemma lem5159048 (s : real -> Prop) (b : real) : (term29 s b) = (term29 s b).
Proof. exact (MK_COMB (@lem5159047 s b) (@lem5159037 s b)). Qed.
Lemma lem5159049 (s : real -> Prop) : (term30 s) = (term30 s).
Proof. exact (fun_ext (fun b : real => @lem5159048 s b)). Qed.
Lemma lem5159050 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159051 (s : real -> Prop) : (term31 s) = (term31 s).
Proof. exact (MK_COMB (@lem5159050) (@lem5159049 s)). Qed.
Lemma lem5159056 (x : real) (s : real -> Prop) : (term32 x s) = (term32 x s).
Proof. exact (eq_refl (term32 x s)). Qed.
Lemma lem5159057 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (fun_ext (fun x : real => @lem5159056 x s)). Qed.
Lemma lem5159058 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159059 (s : real -> Prop) : (term34 s) = (term34 s).
Proof. exact (MK_COMB (@lem5159058) (@lem5159057 s)). Qed.
Lemma lem5159060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5159061 (s : real -> Prop) : (term35 s) = (term35 s).
Proof. exact (MK_COMB (@lem5159060) (@lem5159059 s)). Qed.
Lemma lem5159062 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (MK_COMB (@lem5159061 s) (@lem5159051 s)). Qed.
Lemma lem5159067 (s : real -> Prop) (x : real) (b : real) : (term25 s x b) = (term25 s x b).
Proof. exact (eq_refl (term25 s x b)). Qed.
Lemma lem5159068 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (fun_ext (fun x : real => @lem5159067 s x b)). Qed.
Lemma lem5159069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159070 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (MK_COMB (@lem5159069) (@lem5159068 s b)). Qed.
Lemma lem5159071 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (fun_ext (fun b : real => @lem5159070 s b)). Qed.
Lemma lem5159072 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5159073 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (MK_COMB (@lem5159072) (@lem5159071 s)). Qed.
Lemma lem5159078 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5159079 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5159078 s) (@lem5159073 s)). Qed.
Lemma lem5159080 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5159081 (s : real -> Prop) : (term41 s) = (term41 s).
Proof. exact (MK_COMB (@lem5159080) (@lem5159079 s)). Qed.
Lemma lem5159082 (s : real -> Prop) : (term42 s) = (term42 s).
Proof. exact (MK_COMB (@lem5159081 s) (@lem5159062 s)). Qed.
Lemma lem5159083 : term43 = term43.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5159082 s)). Qed.
Lemma lem5159084 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5159085 : term17 = term17.
Proof. exact (MK_COMB (@lem5159084) (@lem5159083)). Qed.
Lemma lem5159086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5159087 : term16 = term16.
Proof. exact (MK_COMB (@lem5159086) (@lem5159085)). Qed.
Lemma lem5159088 (s : real -> Prop) (b : real) : (term24 s b) = (term24 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5159093 (s : real -> Prop) (x : real) (b : real) : (term25 s x b) = (term25 s x b).
Proof. exact (eq_refl (term25 s x b)). Qed.
Lemma lem5159094 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (fun_ext (fun x : real => @lem5159093 s x b)). Qed.
Lemma lem5159095 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159096 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (MK_COMB (@lem5159095) (@lem5159094 s b)). Qed.
Lemma lem5159101 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5159102 (s : real -> Prop) (b : real) : (term44 s b) = (term44 s b).
Proof. exact (MK_COMB (@lem5159101 s) (@lem5159096 s b)). Qed.
Lemma lem5159103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5159104 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (MK_COMB (@lem5159103) (@lem5159102 s b)). Qed.
Lemma lem5159105 (s : real -> Prop) (b : real) : (term46 s b) = (term46 s b).
Proof. exact (MK_COMB (@lem5159104 s b) (@lem5159088 s b)). Qed.
Lemma lem5159106 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (fun_ext (fun b : real => @lem5159105 s b)). Qed.
Lemma lem5159107 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159108 (s : real -> Prop) : (term8 s) = (term8 s).
Proof. exact (MK_COMB (@lem5159107) (@lem5159106 s)). Qed.
Lemma lem5159109 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5159110 (s : real -> Prop) : (term10 s) = (term10 s).
Proof. exact (MK_COMB (@lem5159109) (@lem5159108 s)). Qed.
Lemma lem5159111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5159112 (s : real -> Prop) : (term18 s) = (term18 s).
Proof. exact (MK_COMB (@lem5159111) (@lem5159110 s)). Qed.
Lemma lem5159113 (s : real -> Prop) : (term19 s) = (term19 s).
Proof. exact (MK_COMB (@lem5159112 s) (@lem5159087)). Qed.
Lemma lem5159114 : term21 = term21.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5159113 s)). Qed.
Lemma lem5159115 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5159116 : term23 = term23.
Proof. exact (MK_COMB (@lem5159115) (@lem5159114)). Qed.
Lemma lem5159195 : term22 = term23.
Proof. exact (TRANS (@lem5159036) (@lem5159116)). Qed.
Lemma lem5159196 : term23 = term22.
Proof. exact (SYM (@lem5159195)). Qed.
Lemma lem5159197 (s : real -> Prop) (h1 : term10 s) : term10 s.
Proof. exact (h1). Qed.
Lemma lem5159198 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5159206 (s : real -> Prop) (x : real) (b : real) : (term25 s x b) = (term48 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5159207 (s : real -> Prop) (b : real) : (term26 s b) = (term49 s b).
Proof. exact (fun_ext (fun x : real => @lem5159206 s x b)). Qed.
Lemma lem5159208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159209 (s : real -> Prop) (b : real) : (term27 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5159208) (@lem5159207 s b)). Qed.
Lemma lem5159211 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5159212 (s : real -> Prop) (b : real) : (term44 s b) = (term51 s b).
Proof. exact (MK_COMB (@lem5159211 s) (@lem5159209 s b)). Qed.
Lemma lem5159213 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (eq_refl (term52 s b)). Qed.
Lemma lem5159214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5159215 (s : real -> Prop) (b : real) : (term53 s b) = (term54 s b).
Proof. exact (MK_COMB (@lem5159214) (@lem5159212 s b)). Qed.
Lemma lem5159216 (s : real -> Prop) (b : real) : (term55 s b) = (term56 s b).
Proof. exact (MK_COMB (@lem5159215 s b) (@lem5159213 s b)). Qed.
Lemma lem5159217 (s : real -> Prop) (b : real) : (term57 s b) = (term55 s b).
Proof. exact (@lem17362 (term44 s b) (term24 s b)). Qed.
Lemma lem5159218 (s : real -> Prop) (b : real) : (term57 s b) = (term56 s b).
Proof. exact (TRANS (@lem5159217 s b) (@lem5159216 s b)). Qed.
Lemma lem5159219 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5159220 (s : real -> Prop) : (term10 s) = (term60 s).
Proof. exact (@lem5159219 (term47 s)). Qed.
Lemma lem5159221 (s : real -> Prop) (b : real) : (term61 s b) = (term46 s b).
Proof. exact (eq_refl (term61 s b)). Qed.
Lemma lem5159222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5159223 (s : real -> Prop) (b : real) : (term62 s b) = (term57 s b).
Proof. exact (MK_COMB (@lem5159222) (@lem5159221 s b)). Qed.
Lemma lem5159224 (s : real -> Prop) (b : real) : (term62 s b) = (term56 s b).
Proof. exact (TRANS (@lem5159223 s b) (@lem5159218 s b)). Qed.
Lemma lem5159225 (s : real -> Prop) : (term63 s) = (term64 s).
Proof. exact (fun_ext (fun b : real => @lem5159224 s b)). Qed.
Lemma lem5159226 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5159227 (s : real -> Prop) : (term60 s) = (term65 s).
Proof. exact (MK_COMB (@lem5159226) (@lem5159225 s)). Qed.
Lemma lem5159328 (s : real -> Prop) : (term10 s) = (term65 s).
Proof. exact (TRANS (@lem5159220 s) (@lem5159227 s)). Qed.
Lemma lem5159329 (s : real -> Prop) (h1 : term10 s) : term65 s.
Proof. exact (EQ_MP (@lem5159328 s) (@lem5159197 s h1)). Qed.
Lemma lem5159332 (s : real -> Prop) : (term66 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5159339 (s : real -> Prop) (x : real) (b : real) : (term67 s x b) = (term68 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5159340 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5159341 (s : real -> Prop) (b : real) : (term69 s b) = (term70 s b).
Proof. exact (@lem5159340 (term26 s b)). Qed.
Lemma lem5159342 (s : real -> Prop) (x : real) (b : real) : (term71 s b x) = (term25 s x b).
Proof. exact (eq_refl (term71 s b x)). Qed.
Lemma lem5159343 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5159344 (s : real -> Prop) (x : real) (b : real) : (term72 s b x) = (term67 s x b).
Proof. exact (MK_COMB (@lem5159343) (@lem5159342 s x b)). Qed.
Lemma lem5159345 (s : real -> Prop) (x : real) (b : real) : (term72 s b x) = (term68 s x b).
Proof. exact (TRANS (@lem5159344 s x b) (@lem5159339 s x b)). Qed.
Lemma lem5159346 (s : real -> Prop) (b : real) : (term73 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5159345 s x b)). Qed.
Lemma lem5159347 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5159348 (s : real -> Prop) (b : real) : (term70 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5159347) (@lem5159346 s b)). Qed.
Lemma lem5159349 (s : real -> Prop) (b : real) : (term69 s b) = (term75 s b).
Proof. exact (TRANS (@lem5159341 s b) (@lem5159348 s b)). Qed.
Lemma lem5159350 (P : real -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5159351 (s : real -> Prop) : (term78 s) = (term79 s).
Proof. exact (@lem5159350 (term37 s)). Qed.
Lemma lem5159352 (s : real -> Prop) (b : real) : (term80 s b) = (term27 s b).
Proof. exact (eq_refl (term80 s b)). Qed.
Lemma lem5159353 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5159354 (s : real -> Prop) (b : real) : (term81 s b) = (term69 s b).
Proof. exact (MK_COMB (@lem5159353) (@lem5159352 s b)). Qed.
Lemma lem5159355 (s : real -> Prop) (b : real) : (term81 s b) = (term75 s b).
Proof. exact (TRANS (@lem5159354 s b) (@lem5159349 s b)). Qed.
Lemma lem5159356 (s : real -> Prop) : (term82 s) = (term83 s).
Proof. exact (fun_ext (fun b : real => @lem5159355 s b)). Qed.
Lemma lem5159357 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159358 (s : real -> Prop) : (term79 s) = (term84 s).
Proof. exact (MK_COMB (@lem5159357) (@lem5159356 s)). Qed.
Lemma lem5159359 (s : real -> Prop) : (term78 s) = (term84 s).
Proof. exact (TRANS (@lem5159351 s) (@lem5159358 s)). Qed.
Lemma lem5159360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159361 (s : real -> Prop) : (term85 s) = (term86 s).
Proof. exact (MK_COMB (@lem5159360) (@lem5159332 s)). Qed.
Lemma lem5159362 (s : real -> Prop) : (term87 s) = (term88 s).
Proof. exact (MK_COMB (@lem5159361 s) (@lem5159359 s)). Qed.
Lemma lem5159363 (s : real -> Prop) : (term89 s) = (term87 s).
Proof. exact (@lem17045 (term90 s) (term38 s)). Qed.
Lemma lem5159364 (s : real -> Prop) : (term89 s) = (term88 s).
Proof. exact (TRANS (@lem5159363 s) (@lem5159362 s)). Qed.
Lemma lem5159371 (x : real) (s : real -> Prop) : (term32 x s) = (term91 x s).
Proof. exact (@lem17265 (@IN real x s) (term92 x s)). Qed.
Lemma lem5159372 (s : real -> Prop) : (term33 s) = (term93 s).
Proof. exact (fun_ext (fun x : real => @lem5159371 x s)). Qed.
Lemma lem5159373 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159374 (s : real -> Prop) : (term34 s) = (term94 s).
Proof. exact (MK_COMB (@lem5159373) (@lem5159372 s)). Qed.
Lemma lem5159381 (s : real -> Prop) (x : real) (b : real) : (term67 s x b) = (term68 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5159382 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5159383 (s : real -> Prop) (b : real) : (term69 s b) = (term70 s b).
Proof. exact (@lem5159382 (term26 s b)). Qed.
Lemma lem5159384 (s : real -> Prop) (x : real) (b : real) : (term71 s b x) = (term25 s x b).
Proof. exact (eq_refl (term71 s b x)). Qed.
Lemma lem5159385 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5159386 (s : real -> Prop) (x : real) (b : real) : (term72 s b x) = (term67 s x b).
Proof. exact (MK_COMB (@lem5159385) (@lem5159384 s x b)). Qed.
Lemma lem5159387 (s : real -> Prop) (x : real) (b : real) : (term72 s b x) = (term68 s x b).
Proof. exact (TRANS (@lem5159386 s x b) (@lem5159381 s x b)). Qed.
Lemma lem5159388 (s : real -> Prop) (b : real) : (term73 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5159387 s x b)). Qed.
Lemma lem5159389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5159390 (s : real -> Prop) (b : real) : (term70 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5159389) (@lem5159388 s b)). Qed.
Lemma lem5159391 (s : real -> Prop) (b : real) : (term69 s b) = (term75 s b).
Proof. exact (TRANS (@lem5159383 s b) (@lem5159390 s b)). Qed.
Lemma lem5159392 (s : real -> Prop) (b : real) : (term24 s b) = (term24 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5159393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159394 (s : real -> Prop) (b : real) : (term95 s b) = (term96 s b).
Proof. exact (MK_COMB (@lem5159393) (@lem5159391 s b)). Qed.
Lemma lem5159395 (s : real -> Prop) (b : real) : (term97 s b) = (term98 s b).
Proof. exact (MK_COMB (@lem5159394 s b) (@lem5159392 s b)). Qed.
Lemma lem5159396 (s : real -> Prop) (b : real) : (term29 s b) = (term97 s b).
Proof. exact (@lem17265 (term27 s b) (term24 s b)). Qed.
Lemma lem5159397 (s : real -> Prop) (b : real) : (term29 s b) = (term98 s b).
Proof. exact (TRANS (@lem5159396 s b) (@lem5159395 s b)). Qed.
Lemma lem5159398 (s : real -> Prop) : (term30 s) = (term99 s).
Proof. exact (fun_ext (fun b : real => @lem5159397 s b)). Qed.
Lemma lem5159399 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159400 (s : real -> Prop) : (term31 s) = (term100 s).
Proof. exact (MK_COMB (@lem5159399) (@lem5159398 s)). Qed.
Lemma lem5159401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5159402 (s : real -> Prop) : (term35 s) = (term101 s).
Proof. exact (MK_COMB (@lem5159401) (@lem5159374 s)). Qed.
Lemma lem5159403 (s : real -> Prop) : (term36 s) = (term102 s).
Proof. exact (MK_COMB (@lem5159402 s) (@lem5159400 s)). Qed.
Lemma lem5159404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159405 (s : real -> Prop) : (term103 s) = (term104 s).
Proof. exact (MK_COMB (@lem5159404) (@lem5159364 s)). Qed.
Lemma lem5159406 (s : real -> Prop) : (term105 s) = (term106 s).
Proof. exact (MK_COMB (@lem5159405 s) (@lem5159403 s)). Qed.
Lemma lem5159407 (s : real -> Prop) : (term42 s) = (term105 s).
Proof. exact (@lem17265 (term40 s) (term36 s)). Qed.
Lemma lem5159408 (s : real -> Prop) : (term42 s) = (term106 s).
Proof. exact (TRANS (@lem5159407 s) (@lem5159406 s)). Qed.
Lemma lem5159409 : term43 = term107.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5159408 s)). Qed.
Lemma lem5159410 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5159411 : term17 = term108.
Proof. exact (MK_COMB (@lem5159410) (@lem5159409)). Qed.
Lemma lem5159658 {A B : Type'} (P : type1413 A B) : (term109 A B P) = (term110 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5159659 (P : type1626) : (term111 P) = (term112 P).
Proof. exact (@lem5159658 real real P). Qed.
Lemma lem5159660 (s : real -> Prop) : (term113 s) = (term114 s).
Proof. exact (@lem5159659 (term115 s)). Qed.
Lemma lem5159661 (s : real -> Prop) (b : real) : (term116 s b) = (term74 s b).
Proof. exact (eq_refl (term116 s b)). Qed.
Lemma lem5159662 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5159663 (s : real -> Prop) (b : real) (x : real) : (term117 s b x) = (term118 s b x).
Proof. exact (MK_COMB (@lem5159661 s b) (@lem5159662 x)). Qed.
Lemma lem5159664 (s : real -> Prop) (x : real) (b : real) : (term118 s b x) = (term68 s x b).
Proof. exact (eq_refl (term118 s b x)). Qed.
Lemma lem5159665 (s : real -> Prop) (x : real) (b : real) : (term117 s b x) = (term68 s x b).
Proof. exact (TRANS (@lem5159663 s b x) (@lem5159664 s x b)). Qed.
Lemma lem5159666 (s : real -> Prop) (b : real) : (term119 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5159665 s x b)). Qed.
Lemma lem5159667 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5159668 (s : real -> Prop) (b : real) : (term120 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5159667) (@lem5159666 s b)). Qed.
Lemma lem5159669 (s : real -> Prop) : (term121 s) = (term83 s).
Proof. exact (fun_ext (fun b : real => @lem5159668 s b)). Qed.
Lemma lem5159670 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159671 (s : real -> Prop) : (term113 s) = (term84 s).
Proof. exact (MK_COMB (@lem5159670) (@lem5159669 s)). Qed.
Lemma lem5159672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5159673 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5159672) (@lem5159671 s)). Qed.
Lemma lem5159674 (s : real -> Prop) (b : real) : (term116 s b) = (term74 s b).
Proof. exact (eq_refl (term116 s b)). Qed.
Lemma lem5159675 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5159676 (s : real -> Prop) (x : real -> real) (b : real) : (term124 s x b) = (term125 s x b).
Proof. exact (MK_COMB (@lem5159674 s b) (@lem5159675 x b)). Qed.
Lemma lem5159677 (s : real -> Prop) (x : real -> real) (b : real) : (term125 s x b) = (term126 s x b).
Proof. exact (eq_refl (term125 s x b)). Qed.
Lemma lem5159678 (s : real -> Prop) (x : real -> real) (b : real) : (term124 s x b) = (term126 s x b).
Proof. exact (TRANS (@lem5159676 s x b) (@lem5159677 s x b)). Qed.
Lemma lem5159679 (s : real -> Prop) (x : real -> real) : (term127 s x) = (term128 s x).
Proof. exact (fun_ext (fun b : real => @lem5159678 s x b)). Qed.
Lemma lem5159680 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159681 (s : real -> Prop) (x : real -> real) : (term129 s x) = (term130 s x).
Proof. exact (MK_COMB (@lem5159680) (@lem5159679 s x)). Qed.
Lemma lem5159682 (s : real -> Prop) : (term131 s) = (term132 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159681 s x)). Qed.
Lemma lem5159683 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159684 (s : real -> Prop) : (term114 s) = (term133 s).
Proof. exact (MK_COMB (@lem5159683) (@lem5159682 s)). Qed.
Lemma lem5159685 (s : real -> Prop) : ((term113 s) = (term114 s)) = ((term84 s) = (term133 s)).
Proof. exact (MK_COMB (@lem5159673 s) (@lem5159684 s)). Qed.
Lemma lem5159686 (s : real -> Prop) : (term84 s) = (term133 s).
Proof. exact (EQ_MP (@lem5159685 s) (@lem5159660 s)). Qed.
Lemma lem5159687 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5159688 (s : real -> Prop) : (term88 s) = (term134 s).
Proof. exact (MK_COMB (@lem5159687 s) (@lem5159686 s)). Qed.
Lemma lem5159690 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5159691 (P : Prop) (Q : type1028) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem5159690 (real -> real) P Q). Qed.
Lemma lem5159692 (s : real -> Prop) : (term139 s) = (term140 s).
Proof. exact (@lem5159691 (s = (@EMPTY real)) (term132 s)). Qed.
Lemma lem5159693 (s : real -> Prop) (x : real -> real) : (term141 s x) = (term130 s x).
Proof. exact (eq_refl (term141 s x)). Qed.
Lemma lem5159694 (s : real -> Prop) : (term142 s) = (term132 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159693 s x)). Qed.
Lemma lem5159695 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159696 (s : real -> Prop) : (term143 s) = (term133 s).
Proof. exact (MK_COMB (@lem5159695) (@lem5159694 s)). Qed.
Lemma lem5159697 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5159698 (s : real -> Prop) : (term139 s) = (term134 s).
Proof. exact (MK_COMB (@lem5159697 s) (@lem5159696 s)). Qed.
Lemma lem5159699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5159700 (s : real -> Prop) : (term144 s) = (term145 s).
Proof. exact (MK_COMB (@lem5159699) (@lem5159698 s)). Qed.
Lemma lem5159701 (s : real -> Prop) (x : real -> real) : (term141 s x) = (term130 s x).
Proof. exact (eq_refl (term141 s x)). Qed.
Lemma lem5159702 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5159703 (s : real -> Prop) (x : real -> real) : (term146 s x) = (term147 s x).
Proof. exact (MK_COMB (@lem5159702 s) (@lem5159701 s x)). Qed.
Lemma lem5159704 (s : real -> Prop) : (term148 s) = (term149 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159703 s x)). Qed.
Lemma lem5159705 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159706 (s : real -> Prop) : (term140 s) = (term150 s).
Proof. exact (MK_COMB (@lem5159705) (@lem5159704 s)). Qed.
Lemma lem5159707 (s : real -> Prop) : ((term139 s) = (term140 s)) = ((term134 s) = (term150 s)).
Proof. exact (MK_COMB (@lem5159700 s) (@lem5159706 s)). Qed.
Lemma lem5159708 (s : real -> Prop) : (term134 s) = (term150 s).
Proof. exact (EQ_MP (@lem5159707 s) (@lem5159692 s)). Qed.
Lemma lem5159709 (s : real -> Prop) : (term88 s) = (term150 s).
Proof. exact (TRANS (@lem5159688 s) (@lem5159708 s)). Qed.
Lemma lem5159710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159711 (s : real -> Prop) : (term104 s) = (term151 s).
Proof. exact (MK_COMB (@lem5159710) (@lem5159709 s)). Qed.
Lemma lem5159713 {A : Type'} (P : A -> Prop) (Q : Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5159714 (P : real -> Prop) (Q : Prop) : (term154 P Q) = (term155 P Q).
Proof. exact (@lem5159713 real P Q). Qed.
Lemma lem5159715 (s : real -> Prop) (b : real) : (term156 s b) = (term157 s b).
Proof. exact (@lem5159714 (term74 s b) (term24 s b)). Qed.
Lemma lem5159716 (s : real -> Prop) (x : real) (b : real) : (term118 s b x) = (term68 s x b).
Proof. exact (eq_refl (term118 s b x)). Qed.
Lemma lem5159717 (s : real -> Prop) (b : real) : (term158 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5159716 s x b)). Qed.
Lemma lem5159718 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5159719 (s : real -> Prop) (b : real) : (term159 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5159718) (@lem5159717 s b)). Qed.
Lemma lem5159720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159721 (s : real -> Prop) (b : real) : (term160 s b) = (term96 s b).
Proof. exact (MK_COMB (@lem5159720) (@lem5159719 s b)). Qed.
Lemma lem5159722 (s : real -> Prop) (b : real) : (term24 s b) = (term24 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5159723 (s : real -> Prop) (b : real) : (term156 s b) = (term98 s b).
Proof. exact (MK_COMB (@lem5159721 s b) (@lem5159722 s b)). Qed.
Lemma lem5159724 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5159725 (s : real -> Prop) (b : real) : (term161 s b) = (term162 s b).
Proof. exact (MK_COMB (@lem5159724) (@lem5159723 s b)). Qed.
Lemma lem5159726 (s : real -> Prop) (x : real) (b : real) : (term118 s b x) = (term68 s x b).
Proof. exact (eq_refl (term118 s b x)). Qed.
Lemma lem5159727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159728 (s : real -> Prop) (x : real) (b : real) : (term163 s b x) = (term164 s x b).
Proof. exact (MK_COMB (@lem5159727) (@lem5159726 s x b)). Qed.
Lemma lem5159729 (s : real -> Prop) (b : real) : (term24 s b) = (term24 s b).
Proof. exact (eq_refl (term24 s b)). Qed.
Lemma lem5159730 (x : real) (s : real -> Prop) (b : real) : (term165 x s b) = (term166 x s b).
Proof. exact (MK_COMB (@lem5159728 s x b) (@lem5159729 s b)). Qed.
Lemma lem5159731 (s : real -> Prop) (b : real) : (term167 s b) = (term168 s b).
Proof. exact (fun_ext (fun x : real => @lem5159730 x s b)). Qed.
Lemma lem5159732 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5159733 (s : real -> Prop) (b : real) : (term157 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5159732) (@lem5159731 s b)). Qed.
Lemma lem5159734 (s : real -> Prop) (b : real) : ((term156 s b) = (term157 s b)) = ((term98 s b) = (term169 s b)).
Proof. exact (MK_COMB (@lem5159725 s b) (@lem5159733 s b)). Qed.
Lemma lem5159735 (s : real -> Prop) (b : real) : (term98 s b) = (term169 s b).
Proof. exact (EQ_MP (@lem5159734 s b) (@lem5159715 s b)). Qed.
Lemma lem5159736 (s : real -> Prop) : (term99 s) = (term170 s).
Proof. exact (fun_ext (fun b : real => @lem5159735 s b)). Qed.
Lemma lem5159737 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159738 (s : real -> Prop) : (term100 s) = (term171 s).
Proof. exact (MK_COMB (@lem5159737) (@lem5159736 s)). Qed.
Lemma lem5159740 {A B : Type'} (P : type1413 A B) : (term109 A B P) = (term110 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5159741 (P : type1626) : (term111 P) = (term112 P).
Proof. exact (@lem5159740 real real P). Qed.
Lemma lem5159742 (s : real -> Prop) : (term172 s) = (term173 s).
Proof. exact (@lem5159741 (term174 s)). Qed.
Lemma lem5159743 (s : real -> Prop) (b : real) : (term175 s b) = (term168 s b).
Proof. exact (eq_refl (term175 s b)). Qed.
Lemma lem5159744 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5159745 (s : real -> Prop) (b : real) (x : real) : (term176 s b x) = (term177 s b x).
Proof. exact (MK_COMB (@lem5159743 s b) (@lem5159744 x)). Qed.
Lemma lem5159746 (x : real) (s : real -> Prop) (b : real) : (term177 s b x) = (term166 x s b).
Proof. exact (eq_refl (term177 s b x)). Qed.
Lemma lem5159747 (x : real) (s : real -> Prop) (b : real) : (term176 s b x) = (term166 x s b).
Proof. exact (TRANS (@lem5159745 s b x) (@lem5159746 x s b)). Qed.
Lemma lem5159748 (s : real -> Prop) (b : real) : (term178 s b) = (term168 s b).
Proof. exact (fun_ext (fun x : real => @lem5159747 x s b)). Qed.
Lemma lem5159749 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5159750 (s : real -> Prop) (b : real) : (term179 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5159749) (@lem5159748 s b)). Qed.
Lemma lem5159751 (s : real -> Prop) : (term180 s) = (term170 s).
Proof. exact (fun_ext (fun b : real => @lem5159750 s b)). Qed.
Lemma lem5159752 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159753 (s : real -> Prop) : (term172 s) = (term171 s).
Proof. exact (MK_COMB (@lem5159752) (@lem5159751 s)). Qed.
Lemma lem5159754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5159755 (s : real -> Prop) : (term181 s) = (term182 s).
Proof. exact (MK_COMB (@lem5159754) (@lem5159753 s)). Qed.
Lemma lem5159756 (s : real -> Prop) (b : real) : (term175 s b) = (term168 s b).
Proof. exact (eq_refl (term175 s b)). Qed.
Lemma lem5159757 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5159758 (s : real -> Prop) (x : real -> real) (b : real) : (term183 s x b) = (term184 s x b).
Proof. exact (MK_COMB (@lem5159756 s b) (@lem5159757 x b)). Qed.
Lemma lem5159759 (x : real -> real) (s : real -> Prop) (b : real) : (term184 s x b) = (term185 x s b).
Proof. exact (eq_refl (term184 s x b)). Qed.
Lemma lem5159760 (x : real -> real) (s : real -> Prop) (b : real) : (term183 s x b) = (term185 x s b).
Proof. exact (TRANS (@lem5159758 s x b) (@lem5159759 x s b)). Qed.
Lemma lem5159761 (x : real -> real) (s : real -> Prop) : (term186 s x) = (term187 x s).
Proof. exact (fun_ext (fun b : real => @lem5159760 x s b)). Qed.
Lemma lem5159762 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159763 (x : real -> real) (s : real -> Prop) : (term188 s x) = (term189 x s).
Proof. exact (MK_COMB (@lem5159762) (@lem5159761 x s)). Qed.
Lemma lem5159764 (s : real -> Prop) : (term190 s) = (term191 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159763 x s)). Qed.
Lemma lem5159765 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159766 (s : real -> Prop) : (term173 s) = (term192 s).
Proof. exact (MK_COMB (@lem5159765) (@lem5159764 s)). Qed.
Lemma lem5159767 (s : real -> Prop) : ((term172 s) = (term173 s)) = ((term171 s) = (term192 s)).
Proof. exact (MK_COMB (@lem5159755 s) (@lem5159766 s)). Qed.
Lemma lem5159768 (s : real -> Prop) : (term171 s) = (term192 s).
Proof. exact (EQ_MP (@lem5159767 s) (@lem5159742 s)). Qed.
Lemma lem5159769 (s : real -> Prop) : (term100 s) = (term192 s).
Proof. exact (TRANS (@lem5159738 s) (@lem5159768 s)). Qed.
Lemma lem5159770 (s : real -> Prop) : (term101 s) = (term101 s).
Proof. exact (eq_refl (term101 s)). Qed.
Lemma lem5159771 (s : real -> Prop) : (term102 s) = (term193 s).
Proof. exact (MK_COMB (@lem5159770 s) (@lem5159769 s)). Qed.
Lemma lem5159773 {A : Type'} (P : Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5159774 (P : Prop) (Q : type1028) : (term196 P Q) = (term197 P Q).
Proof. exact (@lem5159773 (real -> real) P Q). Qed.
Lemma lem5159775 (s : real -> Prop) : (term198 s) = (term199 s).
Proof. exact (@lem5159774 (term94 s) (term191 s)). Qed.
Lemma lem5159776 (x : real -> real) (s : real -> Prop) : (term200 s x) = (term189 x s).
Proof. exact (eq_refl (term200 s x)). Qed.
Lemma lem5159777 (s : real -> Prop) : (term201 s) = (term191 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159776 x s)). Qed.
Lemma lem5159778 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159779 (s : real -> Prop) : (term202 s) = (term192 s).
Proof. exact (MK_COMB (@lem5159778) (@lem5159777 s)). Qed.
Lemma lem5159780 (s : real -> Prop) : (term101 s) = (term101 s).
Proof. exact (eq_refl (term101 s)). Qed.
Lemma lem5159781 (s : real -> Prop) : (term198 s) = (term193 s).
Proof. exact (MK_COMB (@lem5159780 s) (@lem5159779 s)). Qed.
Lemma lem5159782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5159783 (s : real -> Prop) : (term203 s) = (term204 s).
Proof. exact (MK_COMB (@lem5159782) (@lem5159781 s)). Qed.
Lemma lem5159784 (x : real -> real) (s : real -> Prop) : (term200 s x) = (term189 x s).
Proof. exact (eq_refl (term200 s x)). Qed.
Lemma lem5159785 (s : real -> Prop) : (term101 s) = (term101 s).
Proof. exact (eq_refl (term101 s)). Qed.
Lemma lem5159786 (x : real -> real) (s : real -> Prop) : (term205 s x) = (term206 x s).
Proof. exact (MK_COMB (@lem5159785 s) (@lem5159784 x s)). Qed.
Lemma lem5159787 (s : real -> Prop) : (term207 s) = (term208 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159786 x s)). Qed.
Lemma lem5159788 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159789 (s : real -> Prop) : (term199 s) = (term209 s).
Proof. exact (MK_COMB (@lem5159788) (@lem5159787 s)). Qed.
Lemma lem5159790 (s : real -> Prop) : ((term198 s) = (term199 s)) = ((term193 s) = (term209 s)).
Proof. exact (MK_COMB (@lem5159783 s) (@lem5159789 s)). Qed.
Lemma lem5159791 (s : real -> Prop) : (term193 s) = (term209 s).
Proof. exact (EQ_MP (@lem5159790 s) (@lem5159775 s)). Qed.
Lemma lem5159792 (s : real -> Prop) : (term102 s) = (term209 s).
Proof. exact (TRANS (@lem5159771 s) (@lem5159791 s)). Qed.
Lemma lem5159793 (s : real -> Prop) : (term106 s) = (term210 s).
Proof. exact (MK_COMB (@lem5159711 s) (@lem5159792 s)). Qed.
Lemma lem5159795 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5159796 (P : type1028) (Q : type1028) : (term213 P Q) = (term214 P Q).
Proof. exact (@lem5159795 (real -> real) P Q). Qed.
Lemma lem5159797 (s : real -> Prop) : (term215 s) = (term216 s).
Proof. exact (@lem5159796 (term149 s) (term208 s)). Qed.
Lemma lem5159798 (s : real -> Prop) (x : real -> real) : (term217 s x) = (term147 s x).
Proof. exact (eq_refl (term217 s x)). Qed.
Lemma lem5159799 (s : real -> Prop) : (term218 s) = (term149 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159798 s x)). Qed.
Lemma lem5159800 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159801 (s : real -> Prop) : (term219 s) = (term150 s).
Proof. exact (MK_COMB (@lem5159800) (@lem5159799 s)). Qed.
Lemma lem5159802 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159803 (s : real -> Prop) : (term220 s) = (term151 s).
Proof. exact (MK_COMB (@lem5159802) (@lem5159801 s)). Qed.
Lemma lem5159804 (x : real -> real) (s : real -> Prop) : (term221 s x) = (term206 x s).
Proof. exact (eq_refl (term221 s x)). Qed.
Lemma lem5159805 (s : real -> Prop) : (term222 s) = (term208 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159804 x s)). Qed.
Lemma lem5159806 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159807 (s : real -> Prop) : (term223 s) = (term209 s).
Proof. exact (MK_COMB (@lem5159806) (@lem5159805 s)). Qed.
Lemma lem5159808 (s : real -> Prop) : (term215 s) = (term210 s).
Proof. exact (MK_COMB (@lem5159803 s) (@lem5159807 s)). Qed.
Lemma lem5159809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5159810 (s : real -> Prop) : (term224 s) = (term225 s).
Proof. exact (MK_COMB (@lem5159809) (@lem5159808 s)). Qed.
Lemma lem5159811 (s : real -> Prop) (x : real -> real) : (term217 s x) = (term147 s x).
Proof. exact (eq_refl (term217 s x)). Qed.
Lemma lem5159812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159813 (s : real -> Prop) (x : real -> real) : (term226 s x) = (term227 s x).
Proof. exact (MK_COMB (@lem5159812) (@lem5159811 s x)). Qed.
Lemma lem5159814 (x : real -> real) (s : real -> Prop) : (term221 s x) = (term206 x s).
Proof. exact (eq_refl (term221 s x)). Qed.
Lemma lem5159815 (x : real -> real) (s : real -> Prop) : (term228 s x) = (term229 x s).
Proof. exact (MK_COMB (@lem5159813 s x) (@lem5159814 x s)). Qed.
Lemma lem5159816 (s : real -> Prop) : (term230 s) = (term231 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159815 x s)). Qed.
Lemma lem5159817 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159818 (s : real -> Prop) : (term216 s) = (term232 s).
Proof. exact (MK_COMB (@lem5159817) (@lem5159816 s)). Qed.
Lemma lem5159819 (s : real -> Prop) : ((term215 s) = (term216 s)) = ((term210 s) = (term232 s)).
Proof. exact (MK_COMB (@lem5159810 s) (@lem5159818 s)). Qed.
Lemma lem5159820 (s : real -> Prop) : (term210 s) = (term232 s).
Proof. exact (EQ_MP (@lem5159819 s) (@lem5159797 s)). Qed.
Lemma lem5159821 (s : real -> Prop) : (term106 s) = (term232 s).
Proof. exact (TRANS (@lem5159793 s) (@lem5159820 s)). Qed.
Lemma lem5159822 : term107 = term233.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5159821 s)). Qed.
Lemma lem5159823 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5159824 : term108 = term234.
Proof. exact (MK_COMB (@lem5159823) (@lem5159822)). Qed.
Lemma lem5159826 {A B : Type'} (P : type1413 A B) : (term109 A B P) = (term110 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5159827 (P : type1017) : (term235 P) = (term236 P).
Proof. exact (@lem5159826 (real -> Prop) (real -> real) P). Qed.
Lemma lem5159828 : term237 = term238.
Proof. exact (@lem5159827 term239). Qed.
Lemma lem5159829 (s : real -> Prop) : (term240 s) = (term231 s).
Proof. exact (eq_refl (term240 s)). Qed.
Lemma lem5159830 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5159831 (s : real -> Prop) (x : real -> real) : (term241 s x) = (term242 s x).
Proof. exact (MK_COMB (@lem5159829 s) (@lem5159830 x)). Qed.
Lemma lem5159832 (x : real -> real) (s : real -> Prop) : (term242 s x) = (term229 x s).
Proof. exact (eq_refl (term242 s x)). Qed.
Lemma lem5159833 (x : real -> real) (s : real -> Prop) : (term241 s x) = (term229 x s).
Proof. exact (TRANS (@lem5159831 s x) (@lem5159832 x s)). Qed.
Lemma lem5159834 (s : real -> Prop) : (term243 s) = (term231 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5159833 x s)). Qed.
Lemma lem5159835 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5159836 (s : real -> Prop) : (term244 s) = (term232 s).
Proof. exact (MK_COMB (@lem5159835) (@lem5159834 s)). Qed.
Lemma lem5159837 : term245 = term233.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5159836 s)). Qed.
Lemma lem5159838 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5159839 : term237 = term234.
Proof. exact (MK_COMB (@lem5159838) (@lem5159837)). Qed.
Lemma lem5159840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5159841 : term246 = term247.
Proof. exact (MK_COMB (@lem5159840) (@lem5159839)). Qed.
Lemma lem5159842 (s : real -> Prop) : (term240 s) = (term231 s).
Proof. exact (eq_refl (term240 s)). Qed.
Lemma lem5159843 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5159844 (x : type1021) (s : real -> Prop) : (term248 x s) = (term249 x s).
Proof. exact (MK_COMB (@lem5159842 s) (@lem5159843 x s)). Qed.
Lemma lem5159845 (x : type1021) (s : real -> Prop) : (term249 x s) = (term250 x s).
Proof. exact (eq_refl (term249 x s)). Qed.
Lemma lem5159846 (x : type1021) (s : real -> Prop) : (term248 x s) = (term250 x s).
Proof. exact (TRANS (@lem5159844 x s) (@lem5159845 x s)). Qed.
Lemma lem5159847 (x : type1021) : (term251 x) = (term252 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5159846 x s)). Qed.
Lemma lem5159848 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5159849 (x : type1021) : (term253 x) = (term254 x).
Proof. exact (MK_COMB (@lem5159848) (@lem5159847 x)). Qed.
Lemma lem5159850 : term255 = term256.
Proof. exact (fun_ext (fun x : type1021 => @lem5159849 x)). Qed.
Lemma lem5159851 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5159852 : term238 = term257.
Proof. exact (MK_COMB (@lem5159851) (@lem5159850)). Qed.
Lemma lem5159853 : (term237 = term238) = (term234 = term257).
Proof. exact (MK_COMB (@lem5159841) (@lem5159852)). Qed.
Lemma lem5159854 : term234 = term257.
Proof. exact (EQ_MP (@lem5159853) (@lem5159828)). Qed.
Lemma lem5159856 : term108 = term257.
Proof. exact (TRANS (@lem5159824) (@lem5159854)). Qed.
Lemma lem5159857 : term17 = term257.
Proof. exact (TRANS (@lem5159411) (@lem5159856)). Qed.
Lemma lem5159858 (h1 : term17) : term257.
Proof. exact (EQ_MP (@lem5159857) (@lem5159198 h1)). Qed.
Lemma lem5159859 (x : type1021) (h1 : term254 x) : term254 x.
Proof. exact (h1). Qed.
Lemma lem5159860 (s : real -> Prop) (b : real) (h1 : term56 s b) : term56 s b.
Proof. exact (h1). Qed.
Lemma lem5159893 (x : type1021) (s : real -> Prop) (b : real) : (term258 x s b) = (term258 x s b).
Proof. exact (eq_refl (term258 x s b)). Qed.
Lemma lem5159894 (x : type1021) (s : real -> Prop) : (term259 x s) = (term259 x s).
Proof. exact (fun_ext (fun b : real => @lem5159893 x s b)). Qed.
Lemma lem5159895 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159896 (x : type1021) (s : real -> Prop) : (term260 x s) = (term260 x s).
Proof. exact (MK_COMB (@lem5159895) (@lem5159894 x s)). Qed.
Lemma lem5159913 (x : real) (s : real -> Prop) : (term91 x s) = (term91 x s).
Proof. exact (eq_refl (term91 x s)). Qed.
Lemma lem5159914 (s : real -> Prop) : (term93 s) = (term93 s).
Proof. exact (fun_ext (fun x : real => @lem5159913 x s)). Qed.
Lemma lem5159915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159916 (s : real -> Prop) : (term94 s) = (term94 s).
Proof. exact (MK_COMB (@lem5159915) (@lem5159914 s)). Qed.
Lemma lem5159917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5159918 (s : real -> Prop) : (term101 s) = (term101 s).
Proof. exact (MK_COMB (@lem5159917) (@lem5159916 s)). Qed.
Lemma lem5159919 (x : type1021) (s : real -> Prop) : (term261 x s) = (term261 x s).
Proof. exact (MK_COMB (@lem5159918 s) (@lem5159896 x s)). Qed.
Lemma lem5159942 (x : type1021) (s : real -> Prop) (b : real) : (term262 x s b) = (term262 x s b).
Proof. exact (eq_refl (term262 x s b)). Qed.
Lemma lem5159943 (x : type1021) (s : real -> Prop) : (term263 x s) = (term263 x s).
Proof. exact (fun_ext (fun b : real => @lem5159942 x s b)). Qed.
Lemma lem5159944 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159945 (x : type1021) (s : real -> Prop) : (term264 x s) = (term264 x s).
Proof. exact (MK_COMB (@lem5159944) (@lem5159943 x s)). Qed.
Lemma lem5159952 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5159953 (x : type1021) (s : real -> Prop) : (term265 x s) = (term265 x s).
Proof. exact (MK_COMB (@lem5159952 s) (@lem5159945 x s)). Qed.
Lemma lem5159954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5159955 (x : type1021) (s : real -> Prop) : (term266 x s) = (term266 x s).
Proof. exact (MK_COMB (@lem5159954) (@lem5159953 x s)). Qed.
Lemma lem5159956 (x : type1021) (s : real -> Prop) : (term250 x s) = (term250 x s).
Proof. exact (MK_COMB (@lem5159955 x s) (@lem5159919 x s)). Qed.
Lemma lem5159957 (x : type1021) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5159956 x s)). Qed.
Lemma lem5159958 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5159959 (x : type1021) : (term254 x) = (term254 x).
Proof. exact (MK_COMB (@lem5159958) (@lem5159957 x)). Qed.
Lemma lem5159960 (x : type1021) (h1 : term254 x) : term254 x.
Proof. exact (EQ_MP (@lem5159959 x) (@lem5159859 x h1)). Qed.
Lemma lem5159969 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (eq_refl (term52 s b)). Qed.
Lemma lem5159984 (s : real -> Prop) (x : real) (b : real) : (term48 s x b) = (term48 s x b).
Proof. exact (eq_refl (term48 s x b)). Qed.
Lemma lem5159985 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (fun_ext (fun x : real => @lem5159984 s x b)). Qed.
Lemma lem5159986 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5159987 (s : real -> Prop) (b : real) : (term50 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5159986) (@lem5159985 s b)). Qed.
Lemma lem5159996 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5159997 (s : real -> Prop) (b : real) : (term51 s b) = (term51 s b).
Proof. exact (MK_COMB (@lem5159996 s) (@lem5159987 s b)). Qed.
Lemma lem5159998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5159999 (s : real -> Prop) (b : real) : (term54 s b) = (term54 s b).
Proof. exact (MK_COMB (@lem5159998) (@lem5159997 s b)). Qed.
Lemma lem5160000 (s : real -> Prop) (b : real) : (term56 s b) = (term56 s b).
Proof. exact (MK_COMB (@lem5159999 s b) (@lem5159969 s b)). Qed.
Lemma lem5160001 (s : real -> Prop) (b : real) (h1 : term56 s b) : term56 s b.
Proof. exact (EQ_MP (@lem5160000 s b) (@lem5159860 s b h1)). Qed.
Lemma lem5160003 (s : real -> Prop) (b : real) (h1 : term56 s b) : term51 s b.
Proof. exact (proj1 (@lem5160001 s b h1)). Qed.
Lemma lem5160004 (s : real -> Prop) (b : real) (h1 : term56 s b) : term50 s b.
Proof. exact (proj2 (@lem5160003 s b h1)). Qed.
Lemma lem5160007 {A : Type'} (P : Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5160008 (P : Prop) (Q : real -> Prop) : (term269 P Q) = (term270 P Q).
Proof. exact (@lem5160007 real P Q). Qed.
Lemma lem5160009 (x : type1021) (s : real -> Prop) : (term271 x s) = (term272 x s).
Proof. exact (@lem5160008 (s = (@EMPTY real)) (term263 x s)). Qed.
Lemma lem5160010 (x : type1021) (s : real -> Prop) (b : real) : (term273 x s b) = (term262 x s b).
Proof. exact (eq_refl (term273 x s b)). Qed.
Lemma lem5160011 (x : type1021) (s : real -> Prop) : (term274 x s) = (term263 x s).
Proof. exact (fun_ext (fun b : real => @lem5160010 x s b)). Qed.
Lemma lem5160012 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160013 (x : type1021) (s : real -> Prop) : (term275 x s) = (term264 x s).
Proof. exact (MK_COMB (@lem5160012) (@lem5160011 x s)). Qed.
Lemma lem5160014 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5160015 (x : type1021) (s : real -> Prop) : (term271 x s) = (term265 x s).
Proof. exact (MK_COMB (@lem5160014 s) (@lem5160013 x s)). Qed.
Lemma lem5160016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5160017 (x : type1021) (s : real -> Prop) : (term276 x s) = (term277 x s).
Proof. exact (MK_COMB (@lem5160016) (@lem5160015 x s)). Qed.
Lemma lem5160018 (x : type1021) (s : real -> Prop) (b : real) : (term273 x s b) = (term262 x s b).
Proof. exact (eq_refl (term273 x s b)). Qed.
Lemma lem5160019 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5160020 (x : type1021) (s : real -> Prop) (b : real) : (term278 x s b) = (term279 x s b).
Proof. exact (MK_COMB (@lem5160019 s) (@lem5160018 x s b)). Qed.
Lemma lem5160021 (x : type1021) (s : real -> Prop) : (term280 x s) = (term281 x s).
Proof. exact (fun_ext (fun b : real => @lem5160020 x s b)). Qed.
Lemma lem5160022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160023 (x : type1021) (s : real -> Prop) : (term272 x s) = (term282 x s).
Proof. exact (MK_COMB (@lem5160022) (@lem5160021 x s)). Qed.
Lemma lem5160024 (x : type1021) (s : real -> Prop) : ((term271 x s) = (term272 x s)) = ((term265 x s) = (term282 x s)).
Proof. exact (MK_COMB (@lem5160017 x s) (@lem5160023 x s)). Qed.
Lemma lem5160025 (x : type1021) (s : real -> Prop) : (term265 x s) = (term282 x s).
Proof. exact (EQ_MP (@lem5160024 x s) (@lem5160009 x s)). Qed.
Lemma lem5160026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5160027 (x : type1021) (s : real -> Prop) : (term266 x s) = (term283 x s).
Proof. exact (MK_COMB (@lem5160026) (@lem5160025 x s)). Qed.
Lemma lem5160029 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term284 A P Q) = (term285 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5160030 (P : real -> Prop) (Q : real -> Prop) : (term286 P Q) = (term287 P Q).
Proof. exact (@lem5160029 real P Q). Qed.
Lemma lem5160031 (x : type1021) (s : real -> Prop) : (term288 x s) = (term289 x s).
Proof. exact (@lem5160030 (term93 s) (term259 x s)). Qed.
Lemma lem5160032 (b : real) (s : real -> Prop) : (term290 s b) = (term91 b s).
Proof. exact (eq_refl (term290 s b)). Qed.
Lemma lem5160033 (s : real -> Prop) : (term291 s) = (term93 s).
Proof. exact (fun_ext (fun b : real => @lem5160032 b s)). Qed.
Lemma lem5160034 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160035 (s : real -> Prop) : (term292 s) = (term94 s).
Proof. exact (MK_COMB (@lem5160034) (@lem5160033 s)). Qed.
Lemma lem5160036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5160037 (s : real -> Prop) : (term293 s) = (term101 s).
Proof. exact (MK_COMB (@lem5160036) (@lem5160035 s)). Qed.
Lemma lem5160038 (x : type1021) (s : real -> Prop) (b : real) : (term294 x s b) = (term258 x s b).
Proof. exact (eq_refl (term294 x s b)). Qed.
Lemma lem5160039 (x : type1021) (s : real -> Prop) : (term295 x s) = (term259 x s).
Proof. exact (fun_ext (fun b : real => @lem5160038 x s b)). Qed.
Lemma lem5160040 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160041 (x : type1021) (s : real -> Prop) : (term296 x s) = (term260 x s).
Proof. exact (MK_COMB (@lem5160040) (@lem5160039 x s)). Qed.
Lemma lem5160042 (x : type1021) (s : real -> Prop) : (term288 x s) = (term261 x s).
Proof. exact (MK_COMB (@lem5160037 s) (@lem5160041 x s)). Qed.
Lemma lem5160043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5160044 (x : type1021) (s : real -> Prop) : (term297 x s) = (term298 x s).
Proof. exact (MK_COMB (@lem5160043) (@lem5160042 x s)). Qed.
Lemma lem5160045 (b : real) (s : real -> Prop) : (term290 s b) = (term91 b s).
Proof. exact (eq_refl (term290 s b)). Qed.
Lemma lem5160046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5160047 (b : real) (s : real -> Prop) : (term299 s b) = (term300 b s).
Proof. exact (MK_COMB (@lem5160046) (@lem5160045 b s)). Qed.
Lemma lem5160048 (x : type1021) (s : real -> Prop) (b : real) : (term294 x s b) = (term258 x s b).
Proof. exact (eq_refl (term294 x s b)). Qed.
Lemma lem5160049 (x : type1021) (s : real -> Prop) (b : real) : (term301 x s b) = (term302 x s b).
Proof. exact (MK_COMB (@lem5160047 b s) (@lem5160048 x s b)). Qed.
Lemma lem5160050 (x : type1021) (s : real -> Prop) : (term303 x s) = (term304 x s).
Proof. exact (fun_ext (fun b : real => @lem5160049 x s b)). Qed.
Lemma lem5160051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160052 (x : type1021) (s : real -> Prop) : (term289 x s) = (term305 x s).
Proof. exact (MK_COMB (@lem5160051) (@lem5160050 x s)). Qed.
Lemma lem5160053 (x : type1021) (s : real -> Prop) : ((term288 x s) = (term289 x s)) = ((term261 x s) = (term305 x s)).
Proof. exact (MK_COMB (@lem5160044 x s) (@lem5160052 x s)). Qed.
Lemma lem5160054 (x : type1021) (s : real -> Prop) : (term261 x s) = (term305 x s).
Proof. exact (EQ_MP (@lem5160053 x s) (@lem5160031 x s)). Qed.
Lemma lem5160057 (x : type1021) (s : real -> Prop) : (term306 x s) = (term306 x s).
Proof. exact (eq_refl (term306 x s)). Qed.
Lemma lem5160058 (x : type1021) (s : real -> Prop) : (term306 x s) = ((term261 x s) = (term305 x s)).
Proof. exact (eq_refl (term306 x s)). Qed.
Lemma lem5160059 (x : type1021) (s : real -> Prop) : (term307 x s) = (term307 x s).
Proof. exact (eq_refl (term307 x s)). Qed.
Lemma lem5160060 (x : type1021) (s : real -> Prop) : ((term306 x s) = (term306 x s)) = ((term306 x s) = ((term261 x s) = (term305 x s))).
Proof. exact (MK_COMB (@lem5160059 x s) (@lem5160058 x s)). Qed.
Lemma lem5160061 (x : type1021) (s : real -> Prop) : (term306 x s) = ((term261 x s) = (term305 x s)).
Proof. exact (eq_refl (term306 x s)). Qed.
Lemma lem5160062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5160063 (x : type1021) (s : real -> Prop) : (term307 x s) = (term308 x s).
Proof. exact (MK_COMB (@lem5160062) (@lem5160061 x s)). Qed.
Lemma lem5160064 (x : type1021) (s : real -> Prop) : ((term261 x s) = (term305 x s)) = ((term261 x s) = (term305 x s)).
Proof. exact (eq_refl ((term261 x s) = (term305 x s))). Qed.
Lemma lem5160065 (x : type1021) (s : real -> Prop) : ((term306 x s) = ((term261 x s) = (term305 x s))) = (((term261 x s) = (term305 x s)) = ((term261 x s) = (term305 x s))).
Proof. exact (MK_COMB (@lem5160063 x s) (@lem5160064 x s)). Qed.
Lemma lem5160066 (x : type1021) (s : real -> Prop) : ((term306 x s) = (term306 x s)) = (((term261 x s) = (term305 x s)) = ((term261 x s) = (term305 x s))).
Proof. exact (TRANS (@lem5160060 x s) (@lem5160065 x s)). Qed.
Lemma lem5160067 (x : type1021) (s : real -> Prop) : ((term261 x s) = (term305 x s)) = ((term261 x s) = (term305 x s)).
Proof. exact (EQ_MP (@lem5160066 x s) (@lem5160057 x s)). Qed.
Lemma lem5160068 (x : type1021) (s : real -> Prop) : (term261 x s) = (term305 x s).
Proof. exact (EQ_MP (@lem5160067 x s) (@lem5160054 x s)). Qed.
Lemma lem5160069 (x : type1021) (s : real -> Prop) : (term250 x s) = (term309 x s).
Proof. exact (MK_COMB (@lem5160027 x s) (@lem5160068 x s)). Qed.
Lemma lem5160071 {A : Type'} (P : A -> Prop) (Q : Prop) : (term310 A P Q) = (term311 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5160072 (P : real -> Prop) (Q : Prop) : (term312 P Q) = (term313 P Q).
Proof. exact (@lem5160071 real P Q). Qed.
Lemma lem5160073 (x : type1021) (s : real -> Prop) : (term314 x s) = (term315 x s).
Proof. exact (@lem5160072 (term281 x s) (term305 x s)). Qed.
Lemma lem5160074 (x : type1021) (s : real -> Prop) (b : real) : (term316 x s b) = (term279 x s b).
Proof. exact (eq_refl (term316 x s b)). Qed.
Lemma lem5160075 (x : type1021) (s : real -> Prop) : (term317 x s) = (term281 x s).
Proof. exact (fun_ext (fun b : real => @lem5160074 x s b)). Qed.
Lemma lem5160076 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160077 (x : type1021) (s : real -> Prop) : (term318 x s) = (term282 x s).
Proof. exact (MK_COMB (@lem5160076) (@lem5160075 x s)). Qed.
Lemma lem5160078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5160079 (x : type1021) (s : real -> Prop) : (term319 x s) = (term283 x s).
Proof. exact (MK_COMB (@lem5160078) (@lem5160077 x s)). Qed.
Lemma lem5160080 (x : type1021) (s : real -> Prop) : (term305 x s) = (term305 x s).
Proof. exact (eq_refl (term305 x s)). Qed.
Lemma lem5160081 (x : type1021) (s : real -> Prop) : (term314 x s) = (term309 x s).
Proof. exact (MK_COMB (@lem5160079 x s) (@lem5160080 x s)). Qed.
Lemma lem5160082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5160083 (x : type1021) (s : real -> Prop) : (term320 x s) = (term321 x s).
Proof. exact (MK_COMB (@lem5160082) (@lem5160081 x s)). Qed.
Lemma lem5160084 (x : type1021) (s : real -> Prop) (b : real) : (term316 x s b) = (term279 x s b).
Proof. exact (eq_refl (term316 x s b)). Qed.
Lemma lem5160085 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5160086 (x : type1021) (s : real -> Prop) (b : real) : (term322 x s b) = (term323 x s b).
Proof. exact (MK_COMB (@lem5160085) (@lem5160084 x s b)). Qed.
Lemma lem5160087 (x : type1021) (s : real -> Prop) : (term305 x s) = (term305 x s).
Proof. exact (eq_refl (term305 x s)). Qed.
Lemma lem5160088 (b : real) (x : type1021) (s : real -> Prop) : (term324 b x s) = (term325 b x s).
Proof. exact (MK_COMB (@lem5160086 x s b) (@lem5160087 x s)). Qed.
Lemma lem5160089 (x : type1021) (s : real -> Prop) : (term326 x s) = (term327 x s).
Proof. exact (fun_ext (fun b : real => @lem5160088 b x s)). Qed.
Lemma lem5160090 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160091 (x : type1021) (s : real -> Prop) : (term315 x s) = (term328 x s).
Proof. exact (MK_COMB (@lem5160090) (@lem5160089 x s)). Qed.
Lemma lem5160092 (x : type1021) (s : real -> Prop) : ((term314 x s) = (term315 x s)) = ((term309 x s) = (term328 x s)).
Proof. exact (MK_COMB (@lem5160083 x s) (@lem5160091 x s)). Qed.
Lemma lem5160093 (x : type1021) (s : real -> Prop) : (term309 x s) = (term328 x s).
Proof. exact (EQ_MP (@lem5160092 x s) (@lem5160073 x s)). Qed.
Lemma lem5160095 {A : Type'} (P : Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5160096 (P : Prop) (Q : real -> Prop) : (term269 P Q) = (term270 P Q).
Proof. exact (@lem5160095 real P Q). Qed.
Lemma lem5160097 (b : real) (x : type1021) (s : real -> Prop) : (term329 b x s) = (term330 b x s).
Proof. exact (@lem5160096 (term279 x s b) (term304 x s)). Qed.
Lemma lem5160098 (x : type1021) (s : real -> Prop) (b : real) : (term331 x s b) = (term302 x s b).
Proof. exact (eq_refl (term331 x s b)). Qed.
Lemma lem5160099 (x : type1021) (s : real -> Prop) : (term332 x s) = (term304 x s).
Proof. exact (fun_ext (fun b : real => @lem5160098 x s b)). Qed.
Lemma lem5160100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160101 (x : type1021) (s : real -> Prop) : (term333 x s) = (term305 x s).
Proof. exact (MK_COMB (@lem5160100) (@lem5160099 x s)). Qed.
Lemma lem5160102 (x : type1021) (s : real -> Prop) (b : real) : (term323 x s b) = (term323 x s b).
Proof. exact (eq_refl (term323 x s b)). Qed.
Lemma lem5160103 (b : real) (x : type1021) (s : real -> Prop) : (term329 b x s) = (term325 b x s).
Proof. exact (MK_COMB (@lem5160102 x s b) (@lem5160101 x s)). Qed.
Lemma lem5160104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5160105 (b : real) (x : type1021) (s : real -> Prop) : (term334 b x s) = (term335 b x s).
Proof. exact (MK_COMB (@lem5160104) (@lem5160103 b x s)). Qed.
Lemma lem5160106 (x : type1021) (s : real -> Prop) (b' : real) : (term331 x s b') = (term302 x s b').
Proof. exact (eq_refl (term331 x s b')). Qed.
Lemma lem5160107 (x : type1021) (s : real -> Prop) (b : real) : (term323 x s b) = (term323 x s b).
Proof. exact (eq_refl (term323 x s b)). Qed.
Lemma lem5160108 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term336 b x s b') = (term337 b x s b').
Proof. exact (MK_COMB (@lem5160107 x s b) (@lem5160106 x s b')). Qed.
Lemma lem5160109 (b : real) (x : type1021) (s : real -> Prop) : (term338 b x s) = (term339 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5160108 b x s b')). Qed.
Lemma lem5160110 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160111 (b : real) (x : type1021) (s : real -> Prop) : (term330 b x s) = (term340 b x s).
Proof. exact (MK_COMB (@lem5160110) (@lem5160109 b x s)). Qed.
Lemma lem5160112 (b : real) (x : type1021) (s : real -> Prop) : ((term329 b x s) = (term330 b x s)) = ((term325 b x s) = (term340 b x s)).
Proof. exact (MK_COMB (@lem5160105 b x s) (@lem5160111 b x s)). Qed.
Lemma lem5160113 (b : real) (x : type1021) (s : real -> Prop) : (term325 b x s) = (term340 b x s).
Proof. exact (EQ_MP (@lem5160112 b x s) (@lem5160097 b x s)). Qed.
Lemma lem5160114 (x : type1021) (s : real -> Prop) : (term327 x s) = (term341 x s).
Proof. exact (fun_ext (fun b : real => @lem5160113 b x s)). Qed.
Lemma lem5160115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160116 (x : type1021) (s : real -> Prop) : (term328 x s) = (term342 x s).
Proof. exact (MK_COMB (@lem5160115) (@lem5160114 x s)). Qed.
Lemma lem5160117 (x : type1021) (s : real -> Prop) : (term309 x s) = (term342 x s).
Proof. exact (TRANS (@lem5160093 x s) (@lem5160116 x s)). Qed.
Lemma lem5160118 (x : type1021) (s : real -> Prop) : (term250 x s) = (term342 x s).
Proof. exact (TRANS (@lem5160069 x s) (@lem5160117 x s)). Qed.
Lemma lem5160119 (x : type1021) : (term252 x) = (term343 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5160118 x s)). Qed.
Lemma lem5160120 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5160121 (x : type1021) : (term254 x) = (term344 x).
Proof. exact (MK_COMB (@lem5160120) (@lem5160119 x)). Qed.
Lemma lem5160138 (x : type1021) (s : real -> Prop) (b' : real) : (term258 x s b') = (term345 x s b').
Proof. exact (@lem19699 (term346 x b' s) (term347 x s b') (term24 s b')). Qed.
Lemma lem5160147 (b' : real) (s : real -> Prop) : (term300 b' s) = (term300 b' s).
Proof. exact (eq_refl (term300 b' s)). Qed.
Lemma lem5160148 (x : type1021) (s : real -> Prop) (b' : real) : (term302 x s b') = (term348 x s b').
Proof. exact (MK_COMB (@lem5160147 b' s) (@lem5160138 x s b')). Qed.
Lemma lem5160165 (x : type1021) (s : real -> Prop) (b : real) : (term279 x s b) = (term349 x s b).
Proof. exact (@lem19490 (term346 x b s) (s = (@EMPTY real)) (term347 x s b)). Qed.
Lemma lem5160166 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5160167 (x : type1021) (s : real -> Prop) (b : real) : (term323 x s b) = (term350 x s b).
Proof. exact (MK_COMB (@lem5160166) (@lem5160165 x s b)). Qed.
Lemma lem5160168 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term337 b x s b') = (term351 b x s b').
Proof. exact (MK_COMB (@lem5160167 x s b) (@lem5160148 x s b')). Qed.
Lemma lem5160169 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term351 b x s b') = (term352 b x s b').
Proof. exact (@lem19490 (term91 b' s) (term349 x s b) (term345 x s b')). Qed.
Lemma lem5160170 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term353 b x s b') = (term354 b x s b').
Proof. exact (@lem19490 (term355 x s b') (term349 x s b) (term356 x s b')). Qed.
Lemma lem5160177 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term357 b x s b') = (term358 b x s b').
Proof. exact (@lem19699 (term359 x b s) (term360 x s b) (term356 x s b')). Qed.
Lemma lem5160184 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term361 b x s b') = (term362 b x s b').
Proof. exact (@lem19699 (term359 x b s) (term360 x s b) (term355 x s b')). Qed.
Lemma lem5160185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5160186 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term363 b x s b') = (term364 b x s b').
Proof. exact (MK_COMB (@lem5160185) (@lem5160184 b x s b')). Qed.
Lemma lem5160187 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term354 b x s b') = (term365 b x s b').
Proof. exact (MK_COMB (@lem5160186 b x s b') (@lem5160177 b x s b')). Qed.
Lemma lem5160188 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term353 b x s b') = (term365 b x s b').
Proof. exact (TRANS (@lem5160170 b x s b') (@lem5160187 b x s b')). Qed.
Lemma lem5160195 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term366 x b b' s) = (term367 x b b' s).
Proof. exact (@lem19699 (term359 x b s) (term360 x s b) (term91 b' s)). Qed.
Lemma lem5160196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5160197 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term368 x b b' s) = (term369 x b b' s).
Proof. exact (MK_COMB (@lem5160196) (@lem5160195 x b b' s)). Qed.
Lemma lem5160198 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term352 b x s b') = (term370 b x s b').
Proof. exact (MK_COMB (@lem5160197 x b b' s) (@lem5160188 b x s b')). Qed.
Lemma lem5160199 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term351 b x s b') = (term370 b x s b').
Proof. exact (TRANS (@lem5160169 b x s b') (@lem5160198 b x s b')). Qed.
Lemma lem5160200 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term337 b x s b') = (term370 b x s b').
Proof. exact (TRANS (@lem5160168 b x s b') (@lem5160199 b x s b')). Qed.
Lemma lem5160201 (b : real) (x : type1021) (s : real -> Prop) : (term339 b x s) = (term371 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5160200 b x s b')). Qed.
Lemma lem5160202 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160203 (b : real) (x : type1021) (s : real -> Prop) : (term340 b x s) = (term372 b x s).
Proof. exact (MK_COMB (@lem5160202) (@lem5160201 b x s)). Qed.
Lemma lem5160204 (x : type1021) (s : real -> Prop) : (term341 x s) = (term373 x s).
Proof. exact (fun_ext (fun b : real => @lem5160203 b x s)). Qed.
Lemma lem5160205 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160206 (x : type1021) (s : real -> Prop) : (term342 x s) = (term374 x s).
Proof. exact (MK_COMB (@lem5160205) (@lem5160204 x s)). Qed.
Lemma lem5160207 (x : type1021) : (term343 x) = (term375 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5160206 x s)). Qed.
Lemma lem5160208 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5160209 (x : type1021) : (term344 x) = (term376 x).
Proof. exact (MK_COMB (@lem5160208) (@lem5160207 x)). Qed.
Lemma lem5160210 (x : type1021) : (term254 x) = (term376 x).
Proof. exact (TRANS (@lem5160121 x) (@lem5160209 x)). Qed.
Lemma lem5160211 (x : type1021) (h1 : term254 x) : term376 x.
Proof. exact (EQ_MP (@lem5160210 x) (@lem5159960 x h1)). Qed.
Lemma lem5160227 (s : real -> Prop) (x : real) (b : real) : (term48 s x b) = (term48 s x b).
Proof. exact (eq_refl (term48 s x b)). Qed.
Lemma lem5160228 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (fun_ext (fun x : real => @lem5160227 s x b)). Qed.
Lemma lem5160229 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5160231 (s : real -> Prop) (b : real) : (term50 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5160229) (@lem5160228 s b)). Qed.
Lemma lem5160232 (s : real -> Prop) (b : real) (h1 : term56 s b) : term50 s b.
Proof. exact (EQ_MP (@lem5160231 s b) (@lem5160004 s b h1)). Qed.
Lemma lem5160233 (_67457 : real -> Prop) (x : type1021) (h1 : term254 x) : term377 x _67457.
Proof. exact (@lem5160211 x h1 _67457). Qed.
Lemma lem5160234 (x : type1021) (_67457 : real -> Prop) : (term377 x _67457) = (term374 x _67457).
Proof. exact (eq_refl (term377 x _67457)). Qed.
Lemma lem5160235 (_67457 : real -> Prop) (x : type1021) (h1 : term254 x) : term374 x _67457.
Proof. exact (EQ_MP (@lem5160234 x _67457) (@lem5160233 _67457 x h1)). Qed.
Lemma lem5160236 (_67457 : real -> Prop) (_67458 : real) (x : type1021) (h1 : term254 x) : term378 x _67457 _67458.
Proof. exact (@lem5160235 _67457 x h1 _67458). Qed.
Lemma lem5160237 (_67458 : real) (x : type1021) (_67457 : real -> Prop) : (term378 x _67457 _67458) = (term372 _67458 x _67457).
Proof. exact (eq_refl (term378 x _67457 _67458)). Qed.
Lemma lem5160238 (_67458 : real) (_67457 : real -> Prop) (x : type1021) (h1 : term254 x) : term372 _67458 x _67457.
Proof. exact (EQ_MP (@lem5160237 _67458 x _67457) (@lem5160236 _67457 _67458 x h1)). Qed.
Lemma lem5160239 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term379 _67458 x _67457 _67459.
Proof. exact (@lem5160238 _67458 _67457 x h1 _67459). Qed.
Lemma lem5160240 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term379 _67458 x _67457 _67459) = (term370 _67458 x _67457 _67459).
Proof. exact (eq_refl (term379 _67458 x _67457 _67459)). Qed.
Lemma lem5160241 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term370 _67458 x _67457 _67459.
Proof. exact (EQ_MP (@lem5160240 _67458 x _67457 _67459) (@lem5160239 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160242 (_67460 : real) (s : real -> Prop) (b : real) (h1 : term56 s b) : term380 s b _67460.
Proof. exact (@lem5160232 s b h1 _67460). Qed.
Lemma lem5160243 (s : real -> Prop) (_67460 : real) (b : real) : (term380 s b _67460) = (term48 s _67460 b).
Proof. exact (eq_refl (term380 s b _67460)). Qed.
Lemma lem5160245 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term365 _67458 x _67457 _67459.
Proof. exact (proj2 (@lem5160241 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160247 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term358 _67458 x _67457 _67459.
Proof. exact (proj2 (@lem5160245 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160248 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term362 _67458 x _67457 _67459.
Proof. exact (proj1 (@lem5160245 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160249 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term381 _67458 x _67457 _67459.
Proof. exact (proj2 (@lem5160247 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160251 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term382 _67458 x _67457 _67459.
Proof. exact (proj2 (@lem5160248 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160252 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term383 _67458 x _67457 _67459.
Proof. exact (proj1 (@lem5160248 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160258 (s : real -> Prop) (b : real) (h1 : term56 s b) : term90 s.
Proof. exact (proj1 (@lem5160003 s b h1)). Qed.
Lemma lem5160264 (_67460 : real) (s : real -> Prop) (b : real) (h1 : term56 s b) : term48 s _67460 b.
Proof. exact (EQ_MP (@lem5160243 s _67460 b) (@lem5160242 _67460 s b h1)). Qed.
Lemma lem5160295 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term381 _67458 x _67457 _67459) = (term384 _67458 x _67457 _67459).
Proof. exact (@lem5158940 (_67457 = (@EMPTY real)) (term347 x _67457 _67458) (term356 x _67457 _67459)). Qed.
Lemma lem5160296 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term384 _67458 x _67457 _67459.
Proof. exact (EQ_MP (@lem5160295 _67458 x _67457 _67459) (@lem5160249 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160311 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term383 _67458 x _67457 _67459) = (term385 _67458 x _67457 _67459).
Proof. exact (@lem5158940 (_67457 = (@EMPTY real)) (term346 x _67458 _67457) (term355 x _67457 _67459)). Qed.
Lemma lem5160312 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term385 _67458 x _67457 _67459.
Proof. exact (EQ_MP (@lem5160311 _67458 x _67457 _67459) (@lem5160252 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160327 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term382 _67458 x _67457 _67459) = (term386 _67458 x _67457 _67459).
Proof. exact (@lem5158940 (_67457 = (@EMPTY real)) (term347 x _67457 _67458) (term355 x _67457 _67459)). Qed.
Lemma lem5160328 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term386 _67458 x _67457 _67459.
Proof. exact (EQ_MP (@lem5160327 _67458 x _67457 _67459) (@lem5160251 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160428 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (h1). Qed.
Lemma lem5160429 (s : real -> Prop) (h1 : term90 s) : term387 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5160428 s h1). Qed.
Lemma lem5160431 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160432 (s : real -> Prop) : (term387 s) = (term90 s).
Proof. exact (@lem5160431 (s = (@EMPTY real))). Qed.
Lemma lem5160433 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (EQ_MP (@lem5160432 s) (@lem5160429 s h1)). Qed.
Lemma lem5160436 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term389 x b s.
Proof. exact (h1). Qed.
Lemma lem5160437 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term390 x b s.
Proof. exact (fun h0 : term346 x b s => @lem5160436 x b s h1). Qed.
Lemma lem5160439 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160440 (x : type1021) (b : real) (s : real -> Prop) : (term390 x b s) = (term389 x b s).
Proof. exact (@lem5160439 (term346 x b s)). Qed.
Lemma lem5160441 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term389 x b s.
Proof. exact (EQ_MP (@lem5160440 x b s) (@lem5160437 x b s h1)). Qed.
Lemma lem5160443 (s : real -> Prop) (b : real) (h1 : term56 s b) : term52 s b.
Proof. exact (proj2 (@lem5160001 s b h1)). Qed.
Lemma lem5160444 (s : real -> Prop) (b : real) (h1 : term56 s b) : term391 s b.
Proof. exact (fun h0 : term24 s b => @lem5160443 s b h1). Qed.
Lemma lem5160446 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160447 (s : real -> Prop) (b : real) : (term391 s b) = (term52 s b).
Proof. exact (@lem5160446 (term24 s b)). Qed.
Lemma lem5160448 (s : real -> Prop) (b : real) (h1 : term56 s b) : term52 s b.
Proof. exact (EQ_MP (@lem5160447 s b) (@lem5160444 s b h1)). Qed.
Lemma lem5160481 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5160482 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term392 x _67458 _67457 _67459) = (term393 x _67458 _67457 _67459).
Proof. exact (@lem5160481 (_67457 = (@EMPTY real)) (term346 x _67459 _67457) (term394 x _67458 _67457 _67459)). Qed.
Lemma lem5160498 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5160499 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term395 x _67458 _67457 _67459) = (term396 _67458 x _67457 _67459).
Proof. exact (@lem5160498 (term346 x _67458 _67457) (term346 x _67459 _67457) (term24 _67457 _67459)). Qed.
Lemma lem5160515 (_67457 : real -> Prop) : (term86 _67457) = (term86 _67457).
Proof. exact (eq_refl (term86 _67457)). Qed.
Lemma lem5160516 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term393 x _67458 _67457 _67459) = (term385 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160515 _67457) (@lem5160499 _67458 x _67457 _67459)). Qed.
Lemma lem5160527 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term392 x _67458 _67457 _67459) = (term385 _67458 x _67457 _67459).
Proof. exact (TRANS (@lem5160482 x _67458 _67457 _67459) (@lem5160516 _67458 x _67457 _67459)). Qed.
Lemma lem5160528 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term397 _67458 x _67457 _67459) = (term397 _67458 x _67457 _67459).
Proof. exact (eq_refl (term397 _67458 x _67457 _67459)). Qed.
Lemma lem5160529 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : ((term385 _67458 x _67457 _67459) = (term392 x _67458 _67457 _67459)) = ((term385 _67458 x _67457 _67459) = (term385 _67458 x _67457 _67459)).
Proof. exact (MK_COMB (@lem5160528 _67458 x _67457 _67459) (@lem5160527 _67458 x _67457 _67459)). Qed.
Lemma lem5160531 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5160532 (x : Prop) : (x = x) = True.
Proof. exact (@lem5160531 Prop x). Qed.
Lemma lem5160533 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : ((term385 _67458 x _67457 _67459) = (term385 _67458 x _67457 _67459)) = True.
Proof. exact (@lem5160532 (term385 _67458 x _67457 _67459)). Qed.
Lemma lem5160534 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : ((term385 _67458 x _67457 _67459) = (term392 x _67458 _67457 _67459)) = True.
Proof. exact (TRANS (@lem5160529 _67458 x _67457 _67459) (@lem5160533 _67458 x _67457 _67459)). Qed.
Lemma lem5160535 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : True = ((term385 _67458 x _67457 _67459) = (term392 x _67458 _67457 _67459)).
Proof. exact (SYM (@lem5160534 x _67458 _67457 _67459)). Qed.
Lemma lem5160536 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term385 _67458 x _67457 _67459) = (term392 x _67458 _67457 _67459).
Proof. exact (EQ_MP (@lem5160535 x _67458 _67457 _67459) (@lem0)). Qed.
Lemma lem5160537 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term392 x _67458 _67457 _67459.
Proof. exact (EQ_MP (@lem5160536 x _67458 _67457 _67459) (@lem5160312 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160539 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5160540 (_67458 : real) (x : type1021) (_67459 : real) (_67457 : real -> Prop) : (term392 x _67458 _67457 _67459) = (term399 _67458 x _67459 _67457).
Proof. exact (@lem5160539 (term400 x _67458 _67457 _67459) (term346 x _67459 _67457)). Qed.
Lemma lem5160542 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5160543 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term403 x _67458 _67457 _67459) = (term404 x _67458 _67457 _67459).
Proof. exact (@lem5160542 (_67457 = (@EMPTY real)) (term394 x _67458 _67457 _67459)). Qed.
Lemma lem5160545 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5160546 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term405 x _67458 _67457 _67459) = (term406 x _67458 _67457 _67459).
Proof. exact (@lem5160545 (term346 x _67458 _67457) (term24 _67457 _67459)). Qed.
Lemma lem5160547 (_67457 : real -> Prop) : (term39 _67457) = (term39 _67457).
Proof. exact (eq_refl (term39 _67457)). Qed.
Lemma lem5160548 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term404 x _67458 _67457 _67459) = (term407 x _67458 _67457 _67459).
Proof. exact (MK_COMB (@lem5160547 _67457) (@lem5160546 x _67458 _67457 _67459)). Qed.
Lemma lem5160549 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term403 x _67458 _67457 _67459) = (term407 x _67458 _67457 _67459).
Proof. exact (TRANS (@lem5160543 x _67458 _67457 _67459) (@lem5160548 x _67458 _67457 _67459)). Qed.
Lemma lem5160550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5160551 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term408 x _67458 _67457 _67459) = (term409 x _67458 _67457 _67459).
Proof. exact (MK_COMB (@lem5160550) (@lem5160549 x _67458 _67457 _67459)). Qed.
Lemma lem5160552 (x : type1021) (_67459 : real) (_67457 : real -> Prop) : (term346 x _67459 _67457) = (term346 x _67459 _67457).
Proof. exact (eq_refl (term346 x _67459 _67457)). Qed.
Lemma lem5160553 (_67458 : real) (x : type1021) (_67459 : real) (_67457 : real -> Prop) : (term399 _67458 x _67459 _67457) = (term410 _67458 x _67459 _67457).
Proof. exact (MK_COMB (@lem5160551 x _67458 _67457 _67459) (@lem5160552 x _67459 _67457)). Qed.
Lemma lem5160554 (_67458 : real) (x : type1021) (_67459 : real) (_67457 : real -> Prop) : (term392 x _67458 _67457 _67459) = (term410 _67458 x _67459 _67457).
Proof. exact (TRANS (@lem5160540 _67458 x _67459 _67457) (@lem5160553 _67458 x _67459 _67457)). Qed.
Lemma lem5160556 (x : type1021) (s : real -> Prop) (b : real) (h1 : term389 x b s) (h2 : term56 s b) : term411 x s b.
Proof. exact (conj (@lem5160441 x b s h1) (@lem5160448 s b h2)). Qed.
Lemma lem5160557 (x : type1021) (s : real -> Prop) (b : real) (h1 : term90 s) (h2 : term389 x b s) (h3 : term56 s b) : term412 x s b.
Proof. exact (conj (@lem5160433 s h1) (@lem5160556 x s b h2 h3)). Qed.
Lemma lem5160559 (_67458 : real) (_67459 : real) (_67457 : real -> Prop) (x : type1021) (h1 : term254 x) : term410 _67458 x _67459 _67457.
Proof. exact (EQ_MP (@lem5160554 _67458 x _67459 _67457) (@lem5160537 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160560 (b : real) (s : real -> Prop) (x : type1021) (h1 : term254 x) : term413 x b s.
Proof. exact (@lem5160559 b b s x h1). Qed.
Lemma lem5160563 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term389 x b s) (h4 : term56 s b) : term346 x b s.
Proof. exact (@lem5160560 b s x h1 (@lem5160557 x s b h2 h3 h4)). Qed.
Lemma lem5160564 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term414 x b s.
Proof. exact (fun h0 : term389 x b s => @lem5160563 x s b h1 h2 h0 h3). Qed.
Lemma lem5160566 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5160567 (x : type1021) (b : real) (s : real -> Prop) : (term414 x b s) = (term346 x b s).
Proof. exact (@lem5160566 (term346 x b s)). Qed.
Lemma lem5160568 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term346 x b s.
Proof. exact (EQ_MP (@lem5160567 x b s) (@lem5160564 x s b h1 h2 h3)). Qed.
Lemma lem5160574 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5160575 (b : real) (_67460 : real) (s : real -> Prop) : (term48 s _67460 b) = (term416 b _67460 s).
Proof. exact (@lem5160574 (real_le _67460 b) (term417 _67460 s)). Qed.
Lemma lem5160581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5160582 (b : real) (_67460 : real) (s : real -> Prop) : (term418 s _67460 b) = (term419 b _67460 s).
Proof. exact (MK_COMB (@lem5160581) (@lem5160575 b _67460 s)). Qed.
Lemma lem5160588 (b : real) (_67460 : real) (s : real -> Prop) : (term416 b _67460 s) = (term416 b _67460 s).
Proof. exact (eq_refl (term416 b _67460 s)). Qed.
Lemma lem5160589 (b : real) (_67460 : real) (s : real -> Prop) : ((term48 s _67460 b) = (term416 b _67460 s)) = ((term416 b _67460 s) = (term416 b _67460 s)).
Proof. exact (MK_COMB (@lem5160582 b _67460 s) (@lem5160588 b _67460 s)). Qed.
Lemma lem5160591 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5160592 (x : Prop) : (x = x) = True.
Proof. exact (@lem5160591 Prop x). Qed.
Lemma lem5160593 (b : real) (_67460 : real) (s : real -> Prop) : ((term416 b _67460 s) = (term416 b _67460 s)) = True.
Proof. exact (@lem5160592 (term416 b _67460 s)). Qed.
Lemma lem5160594 (b : real) (_67460 : real) (s : real -> Prop) : ((term48 s _67460 b) = (term416 b _67460 s)) = True.
Proof. exact (TRANS (@lem5160589 b _67460 s) (@lem5160593 b _67460 s)). Qed.
Lemma lem5160595 (b : real) (_67460 : real) (s : real -> Prop) : True = ((term48 s _67460 b) = (term416 b _67460 s)).
Proof. exact (SYM (@lem5160594 b _67460 s)). Qed.
Lemma lem5160596 (b : real) (_67460 : real) (s : real -> Prop) : (term48 s _67460 b) = (term416 b _67460 s).
Proof. exact (EQ_MP (@lem5160595 b _67460 s) (@lem0)). Qed.
Lemma lem5160597 (_67460 : real) (s : real -> Prop) (b : real) (h1 : term56 s b) : term416 b _67460 s.
Proof. exact (EQ_MP (@lem5160596 b _67460 s) (@lem5160264 _67460 s b h1)). Qed.
Lemma lem5160599 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5160600 (s : real -> Prop) (_67460 : real) (b : real) : (term416 b _67460 s) = (term420 s _67460 b).
Proof. exact (@lem5160599 (term417 _67460 s) (real_le _67460 b)). Qed.
Lemma lem5160602 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5160603 (_67460 : real) (s : real -> Prop) : (term422 _67460 s) = (@IN real _67460 s).
Proof. exact (@lem5160602 (@IN real _67460 s)). Qed.
Lemma lem5160604 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5160605 (_67460 : real) (s : real -> Prop) : (term423 _67460 s) = (term424 _67460 s).
Proof. exact (MK_COMB (@lem5160604) (@lem5160603 _67460 s)). Qed.
Lemma lem5160606 (_67460 : real) (b : real) : (real_le _67460 b) = (real_le _67460 b).
Proof. exact (eq_refl (real_le _67460 b)). Qed.
Lemma lem5160607 (s : real -> Prop) (_67460 : real) (b : real) : (term420 s _67460 b) = (term25 s _67460 b).
Proof. exact (MK_COMB (@lem5160605 _67460 s) (@lem5160606 _67460 b)). Qed.
Lemma lem5160608 (s : real -> Prop) (_67460 : real) (b : real) : (term416 b _67460 s) = (term25 s _67460 b).
Proof. exact (TRANS (@lem5160600 s _67460 b) (@lem5160607 s _67460 b)). Qed.
Lemma lem5160611 (_67460 : real) (s : real -> Prop) (b : real) (h1 : term56 s b) : term25 s _67460 b.
Proof. exact (EQ_MP (@lem5160608 s _67460 b) (@lem5160597 _67460 s b h1)). Qed.
Lemma lem5160612 (x : type1021) (s : real -> Prop) (b : real) (h1 : term56 s b) : term425 x s b.
Proof. exact (@lem5160611 (x s b) s b h1). Qed.
Lemma lem5160615 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term426 x s b.
Proof. exact (@lem5160612 x s b h3 (@lem5160568 x s b h1 h2 h3)). Qed.
Lemma lem5160616 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term427 x s b.
Proof. exact (fun h0 : term347 x s b => @lem5160615 x s b h1 h2 h3). Qed.
Lemma lem5160618 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5160619 (x : type1021) (s : real -> Prop) (b : real) : (term427 x s b) = (term426 x s b).
Proof. exact (@lem5160618 (term426 x s b)). Qed.
Lemma lem5160620 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term426 x s b.
Proof. exact (EQ_MP (@lem5160619 x s b) (@lem5160616 x s b h1 h2 h3)). Qed.
Lemma lem5160623 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (h1). Qed.
Lemma lem5160624 (s : real -> Prop) (h1 : term90 s) : term387 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5160623 s h1). Qed.
Lemma lem5160626 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160627 (s : real -> Prop) : (term387 s) = (term90 s).
Proof. exact (@lem5160626 (s = (@EMPTY real))). Qed.
Lemma lem5160628 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (EQ_MP (@lem5160627 s) (@lem5160624 s h1)). Qed.
Lemma lem5160631 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (h1). Qed.
Lemma lem5160632 (s : real -> Prop) (h1 : term90 s) : term387 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5160631 s h1). Qed.
Lemma lem5160634 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160635 (s : real -> Prop) : (term387 s) = (term90 s).
Proof. exact (@lem5160634 (s = (@EMPTY real))). Qed.
Lemma lem5160636 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (EQ_MP (@lem5160635 s) (@lem5160632 s h1)). Qed.
Lemma lem5160639 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term389 x b s.
Proof. exact (h1). Qed.
Lemma lem5160640 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term390 x b s.
Proof. exact (fun h0 : term346 x b s => @lem5160639 x b s h1). Qed.
Lemma lem5160642 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160643 (x : type1021) (b : real) (s : real -> Prop) : (term390 x b s) = (term389 x b s).
Proof. exact (@lem5160642 (term346 x b s)). Qed.
Lemma lem5160644 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term389 x b s.
Proof. exact (EQ_MP (@lem5160643 x b s) (@lem5160640 x b s h1)). Qed.
Lemma lem5160646 (s : real -> Prop) (b : real) (h1 : term56 s b) : term52 s b.
Proof. exact (proj2 (@lem5160001 s b h1)). Qed.
Lemma lem5160647 (s : real -> Prop) (b : real) (h1 : term56 s b) : term391 s b.
Proof. exact (fun h0 : term24 s b => @lem5160646 s b h1). Qed.
Lemma lem5160649 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160650 (s : real -> Prop) (b : real) : (term391 s b) = (term52 s b).
Proof. exact (@lem5160649 (term24 s b)). Qed.
Lemma lem5160651 (s : real -> Prop) (b : real) (h1 : term56 s b) : term52 s b.
Proof. exact (EQ_MP (@lem5160650 s b) (@lem5160647 s b h1)). Qed.
Lemma lem5160652 (x : type1021) (s : real -> Prop) (b : real) (h1 : term389 x b s) (h2 : term56 s b) : term411 x s b.
Proof. exact (conj (@lem5160644 x b s h1) (@lem5160651 s b h2)). Qed.
Lemma lem5160653 (x : type1021) (s : real -> Prop) (b : real) (h1 : term90 s) (h2 : term389 x b s) (h3 : term56 s b) : term412 x s b.
Proof. exact (conj (@lem5160636 s h1) (@lem5160652 x s b h2 h3)). Qed.
Lemma lem5160655 (_67458 : real) (_67459 : real) (_67457 : real -> Prop) (x : type1021) (h1 : term254 x) : term410 _67458 x _67459 _67457.
Proof. exact (EQ_MP (@lem5160554 _67458 x _67459 _67457) (@lem5160537 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160656 (b : real) (s : real -> Prop) (x : type1021) (h1 : term254 x) : term413 x b s.
Proof. exact (@lem5160655 b b s x h1). Qed.
Lemma lem5160659 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term389 x b s) (h4 : term56 s b) : term346 x b s.
Proof. exact (@lem5160656 b s x h1 (@lem5160653 x s b h2 h3 h4)). Qed.
Lemma lem5160660 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term414 x b s.
Proof. exact (fun h0 : term389 x b s => @lem5160659 x s b h1 h2 h0 h3). Qed.
Lemma lem5160662 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5160663 (x : type1021) (b : real) (s : real -> Prop) : (term414 x b s) = (term346 x b s).
Proof. exact (@lem5160662 (term346 x b s)). Qed.
Lemma lem5160664 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term346 x b s.
Proof. exact (EQ_MP (@lem5160663 x b s) (@lem5160660 x s b h1 h2 h3)). Qed.
Lemma lem5160666 (_67460 : real) (s : real -> Prop) (b : real) (h1 : term56 s b) : term25 s _67460 b.
Proof. exact (EQ_MP (@lem5160608 s _67460 b) (@lem5160597 _67460 s b h1)). Qed.
Lemma lem5160667 (x : type1021) (s : real -> Prop) (b : real) (h1 : term56 s b) : term425 x s b.
Proof. exact (@lem5160666 (x s b) s b h1). Qed.
Lemma lem5160670 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term426 x s b.
Proof. exact (@lem5160667 x s b h3 (@lem5160664 x s b h1 h2 h3)). Qed.
Lemma lem5160671 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term427 x s b.
Proof. exact (fun h0 : term347 x s b => @lem5160670 x s b h1 h2 h3). Qed.
Lemma lem5160673 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5160674 (x : type1021) (s : real -> Prop) (b : real) : (term427 x s b) = (term426 x s b).
Proof. exact (@lem5160673 (term426 x s b)). Qed.
Lemma lem5160675 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term426 x s b.
Proof. exact (EQ_MP (@lem5160674 x s b) (@lem5160671 x s b h1 h2 h3)). Qed.
Lemma lem5160677 (s : real -> Prop) (b : real) (h1 : term56 s b) : term52 s b.
Proof. exact (proj2 (@lem5160001 s b h1)). Qed.
Lemma lem5160678 (s : real -> Prop) (b : real) (h1 : term56 s b) : term391 s b.
Proof. exact (fun h0 : term24 s b => @lem5160677 s b h1). Qed.
Lemma lem5160680 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160681 (s : real -> Prop) (b : real) : (term391 s b) = (term52 s b).
Proof. exact (@lem5160680 (term24 s b)). Qed.
Lemma lem5160682 (s : real -> Prop) (b : real) (h1 : term56 s b) : term52 s b.
Proof. exact (EQ_MP (@lem5160681 s b) (@lem5160678 s b h1)). Qed.
Lemma lem5160710 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5160711 (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term356 x _67457 _67459) = (term428 x _67457 _67459).
Proof. exact (@lem5160710 (term24 _67457 _67459) (term347 x _67457 _67459)). Qed.
Lemma lem5160717 (x : type1021) (_67457 : real -> Prop) (_67458 : real) : (term429 x _67457 _67458) = (term429 x _67457 _67458).
Proof. exact (eq_refl (term429 x _67457 _67458)). Qed.
Lemma lem5160718 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term430 _67458 x _67457 _67459) = (term431 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160717 x _67457 _67458) (@lem5160711 x _67457 _67459)). Qed.
Lemma lem5160722 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5160723 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term431 _67458 x _67457 _67459) = (term432 _67458 x _67457 _67459).
Proof. exact (@lem5160722 (term24 _67457 _67459) (term347 x _67457 _67458) (term347 x _67457 _67459)). Qed.
Lemma lem5160739 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term430 _67458 x _67457 _67459) = (term432 _67458 x _67457 _67459).
Proof. exact (TRANS (@lem5160718 _67458 x _67457 _67459) (@lem5160723 _67458 x _67457 _67459)). Qed.
Lemma lem5160740 (_67457 : real -> Prop) : (term86 _67457) = (term86 _67457).
Proof. exact (eq_refl (term86 _67457)). Qed.
Lemma lem5160741 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term384 _67458 x _67457 _67459) = (term433 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160740 _67457) (@lem5160739 _67458 x _67457 _67459)). Qed.
Lemma lem5160752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5160753 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term434 _67458 x _67457 _67459) = (term435 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160752) (@lem5160741 _67458 x _67457 _67459)). Qed.
Lemma lem5160757 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5160758 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term436 x _67458 _67457 _67459) = (term437 x _67458 _67457 _67459).
Proof. exact (@lem5160757 (_67457 = (@EMPTY real)) (term347 x _67457 _67459) (term438 x _67458 _67457 _67459)). Qed.
Lemma lem5160774 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5160775 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term439 x _67458 _67457 _67459) = (term430 _67458 x _67457 _67459).
Proof. exact (@lem5160774 (term347 x _67457 _67458) (term347 x _67457 _67459) (term24 _67457 _67459)). Qed.
Lemma lem5160789 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5160790 (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term356 x _67457 _67459) = (term428 x _67457 _67459).
Proof. exact (@lem5160789 (term24 _67457 _67459) (term347 x _67457 _67459)). Qed.
Lemma lem5160796 (x : type1021) (_67457 : real -> Prop) (_67458 : real) : (term429 x _67457 _67458) = (term429 x _67457 _67458).
Proof. exact (eq_refl (term429 x _67457 _67458)). Qed.
Lemma lem5160797 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term430 _67458 x _67457 _67459) = (term431 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160796 x _67457 _67458) (@lem5160790 x _67457 _67459)). Qed.
Lemma lem5160801 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5160802 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term431 _67458 x _67457 _67459) = (term432 _67458 x _67457 _67459).
Proof. exact (@lem5160801 (term24 _67457 _67459) (term347 x _67457 _67458) (term347 x _67457 _67459)). Qed.
Lemma lem5160818 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term430 _67458 x _67457 _67459) = (term432 _67458 x _67457 _67459).
Proof. exact (TRANS (@lem5160797 _67458 x _67457 _67459) (@lem5160802 _67458 x _67457 _67459)). Qed.
Lemma lem5160819 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term439 x _67458 _67457 _67459) = (term432 _67458 x _67457 _67459).
Proof. exact (TRANS (@lem5160775 _67458 x _67457 _67459) (@lem5160818 _67458 x _67457 _67459)). Qed.
Lemma lem5160820 (_67457 : real -> Prop) : (term86 _67457) = (term86 _67457).
Proof. exact (eq_refl (term86 _67457)). Qed.
Lemma lem5160821 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term437 x _67458 _67457 _67459) = (term433 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160820 _67457) (@lem5160819 _67458 x _67457 _67459)). Qed.
Lemma lem5160832 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term436 x _67458 _67457 _67459) = (term433 _67458 x _67457 _67459).
Proof. exact (TRANS (@lem5160758 x _67458 _67457 _67459) (@lem5160821 _67458 x _67457 _67459)). Qed.
Lemma lem5160833 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : ((term384 _67458 x _67457 _67459) = (term436 x _67458 _67457 _67459)) = ((term433 _67458 x _67457 _67459) = (term433 _67458 x _67457 _67459)).
Proof. exact (MK_COMB (@lem5160753 _67458 x _67457 _67459) (@lem5160832 _67458 x _67457 _67459)). Qed.
Lemma lem5160835 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5160836 (x : Prop) : (x = x) = True.
Proof. exact (@lem5160835 Prop x). Qed.
Lemma lem5160837 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : ((term433 _67458 x _67457 _67459) = (term433 _67458 x _67457 _67459)) = True.
Proof. exact (@lem5160836 (term433 _67458 x _67457 _67459)). Qed.
Lemma lem5160838 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : ((term384 _67458 x _67457 _67459) = (term436 x _67458 _67457 _67459)) = True.
Proof. exact (TRANS (@lem5160833 _67458 x _67457 _67459) (@lem5160837 _67458 x _67457 _67459)). Qed.
Lemma lem5160839 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : True = ((term384 _67458 x _67457 _67459) = (term436 x _67458 _67457 _67459)).
Proof. exact (SYM (@lem5160838 x _67458 _67457 _67459)). Qed.
Lemma lem5160840 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term384 _67458 x _67457 _67459) = (term436 x _67458 _67457 _67459).
Proof. exact (EQ_MP (@lem5160839 x _67458 _67457 _67459) (@lem0)). Qed.
Lemma lem5160841 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term436 x _67458 _67457 _67459.
Proof. exact (EQ_MP (@lem5160840 x _67458 _67457 _67459) (@lem5160296 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160843 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5160844 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term436 x _67458 _67457 _67459) = (term440 _67458 x _67457 _67459).
Proof. exact (@lem5160843 (term441 x _67458 _67457 _67459) (term347 x _67457 _67459)). Qed.
Lemma lem5160846 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5160847 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term442 x _67458 _67457 _67459) = (term443 x _67458 _67457 _67459).
Proof. exact (@lem5160846 (_67457 = (@EMPTY real)) (term438 x _67458 _67457 _67459)). Qed.
Lemma lem5160849 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5160850 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term444 x _67458 _67457 _67459) = (term445 x _67458 _67457 _67459).
Proof. exact (@lem5160849 (term347 x _67457 _67458) (term24 _67457 _67459)). Qed.
Lemma lem5160852 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5160853 (x : type1021) (_67457 : real -> Prop) (_67458 : real) : (term446 x _67457 _67458) = (term426 x _67457 _67458).
Proof. exact (@lem5160852 (term426 x _67457 _67458)). Qed.
Lemma lem5160854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5160855 (x : type1021) (_67457 : real -> Prop) (_67458 : real) : (term447 x _67457 _67458) = (term448 x _67457 _67458).
Proof. exact (MK_COMB (@lem5160854) (@lem5160853 x _67457 _67458)). Qed.
Lemma lem5160856 (_67457 : real -> Prop) (_67459 : real) : (term52 _67457 _67459) = (term52 _67457 _67459).
Proof. exact (eq_refl (term52 _67457 _67459)). Qed.
Lemma lem5160857 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term445 x _67458 _67457 _67459) = (term449 x _67458 _67457 _67459).
Proof. exact (MK_COMB (@lem5160855 x _67457 _67458) (@lem5160856 _67457 _67459)). Qed.
Lemma lem5160858 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term444 x _67458 _67457 _67459) = (term449 x _67458 _67457 _67459).
Proof. exact (TRANS (@lem5160850 x _67458 _67457 _67459) (@lem5160857 x _67458 _67457 _67459)). Qed.
Lemma lem5160859 (_67457 : real -> Prop) : (term39 _67457) = (term39 _67457).
Proof. exact (eq_refl (term39 _67457)). Qed.
Lemma lem5160860 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term443 x _67458 _67457 _67459) = (term450 x _67458 _67457 _67459).
Proof. exact (MK_COMB (@lem5160859 _67457) (@lem5160858 x _67458 _67457 _67459)). Qed.
Lemma lem5160861 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term442 x _67458 _67457 _67459) = (term450 x _67458 _67457 _67459).
Proof. exact (TRANS (@lem5160847 x _67458 _67457 _67459) (@lem5160860 x _67458 _67457 _67459)). Qed.
Lemma lem5160862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5160863 (x : type1021) (_67458 : real) (_67457 : real -> Prop) (_67459 : real) : (term451 x _67458 _67457 _67459) = (term452 x _67458 _67457 _67459).
Proof. exact (MK_COMB (@lem5160862) (@lem5160861 x _67458 _67457 _67459)). Qed.
Lemma lem5160864 (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term347 x _67457 _67459) = (term347 x _67457 _67459).
Proof. exact (eq_refl (term347 x _67457 _67459)). Qed.
Lemma lem5160865 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term440 _67458 x _67457 _67459) = (term453 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160863 x _67458 _67457 _67459) (@lem5160864 x _67457 _67459)). Qed.
Lemma lem5160866 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term436 x _67458 _67457 _67459) = (term453 _67458 x _67457 _67459).
Proof. exact (TRANS (@lem5160844 _67458 x _67457 _67459) (@lem5160865 _67458 x _67457 _67459)). Qed.
Lemma lem5160868 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term454 x s b.
Proof. exact (conj (@lem5160675 x s b h1 h2 h3) (@lem5160682 s b h3)). Qed.
Lemma lem5160869 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term455 x s b.
Proof. exact (conj (@lem5160628 s h2) (@lem5160868 x s b h1 h2 h3)). Qed.
Lemma lem5160871 (_67458 : real) (_67457 : real -> Prop) (_67459 : real) (x : type1021) (h1 : term254 x) : term453 _67458 x _67457 _67459.
Proof. exact (EQ_MP (@lem5160866 _67458 x _67457 _67459) (@lem5160841 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160872 (s : real -> Prop) (b : real) (x : type1021) (h1 : term254 x) : term456 x s b.
Proof. exact (@lem5160871 b s b x h1). Qed.
Lemma lem5160875 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term347 x s b.
Proof. exact (@lem5160872 s b x h1 (@lem5160869 x s b h1 h2 h3)). Qed.
Lemma lem5160876 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term457 x s b.
Proof. exact (fun h0 : term426 x s b => @lem5160875 x s b h1 h2 h3). Qed.
Lemma lem5160878 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160879 (x : type1021) (s : real -> Prop) (b : real) : (term457 x s b) = (term347 x s b).
Proof. exact (@lem5160878 (term426 x s b)). Qed.
Lemma lem5160880 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term347 x s b.
Proof. exact (EQ_MP (@lem5160879 x s b) (@lem5160876 x s b h1 h2 h3)). Qed.
Lemma lem5160882 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5160885 (b : real) (_67460 : real) (s : real -> Prop) : (term48 s _67460 b) = (term458 b _67460 s).
Proof. exact (@lem5160882 (real_le _67460 b) (term417 _67460 s)). Qed.
Lemma lem5160888 (_67460 : real) (s : real -> Prop) (b : real) (h1 : term56 s b) : term458 b _67460 s.
Proof. exact (EQ_MP (@lem5160885 b _67460 s) (@lem5160264 _67460 s b h1)). Qed.
Lemma lem5160889 (x : type1021) (s : real -> Prop) (b : real) (h1 : term56 s b) : term459 x b s.
Proof. exact (@lem5160888 (x s b) s b h1). Qed.
Lemma lem5160892 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term389 x b s.
Proof. exact (@lem5160889 x s b h3 (@lem5160880 x s b h1 h2 h3)). Qed.
Lemma lem5160893 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term390 x b s.
Proof. exact (fun h0 : term346 x b s => @lem5160892 x s b h1 h2 h3). Qed.
Lemma lem5160895 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160896 (x : type1021) (b : real) (s : real -> Prop) : (term390 x b s) = (term389 x b s).
Proof. exact (@lem5160895 (term346 x b s)). Qed.
Lemma lem5160897 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term389 x b s.
Proof. exact (EQ_MP (@lem5160896 x b s) (@lem5160893 x s b h1 h2 h3)). Qed.
Lemma lem5160899 (s : real -> Prop) (b : real) (h1 : term56 s b) : term52 s b.
Proof. exact (proj2 (@lem5160001 s b h1)). Qed.
Lemma lem5160900 (s : real -> Prop) (b : real) (h1 : term56 s b) : term391 s b.
Proof. exact (fun h0 : term24 s b => @lem5160899 s b h1). Qed.
Lemma lem5160902 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5160903 (s : real -> Prop) (b : real) : (term391 s b) = (term52 s b).
Proof. exact (@lem5160902 (term24 s b)). Qed.
Lemma lem5160904 (s : real -> Prop) (b : real) (h1 : term56 s b) : term52 s b.
Proof. exact (EQ_MP (@lem5160903 s b) (@lem5160900 s b h1)). Qed.
Lemma lem5160906 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5160907 (_67458 : real) (x : type1021) (_67459 : real) (_67457 : real -> Prop) : (term386 _67458 x _67457 _67459) = (term460 _67458 x _67459 _67457).
Proof. exact (@lem5160906 (term461 _67458 x _67457 _67459) (_67457 = (@EMPTY real))). Qed.
Lemma lem5160909 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5160910 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term462 _67458 x _67457 _67459) = (term463 _67458 x _67457 _67459).
Proof. exact (@lem5160909 (term347 x _67457 _67458) (term355 x _67457 _67459)). Qed.
Lemma lem5160912 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5160913 (x : type1021) (_67457 : real -> Prop) (_67458 : real) : (term446 x _67457 _67458) = (term426 x _67457 _67458).
Proof. exact (@lem5160912 (term426 x _67457 _67458)). Qed.
Lemma lem5160914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5160915 (x : type1021) (_67457 : real -> Prop) (_67458 : real) : (term447 x _67457 _67458) = (term448 x _67457 _67458).
Proof. exact (MK_COMB (@lem5160914) (@lem5160913 x _67457 _67458)). Qed.
Lemma lem5160917 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5160918 (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term464 x _67457 _67459) = (term411 x _67457 _67459).
Proof. exact (@lem5160917 (term346 x _67459 _67457) (term24 _67457 _67459)). Qed.
Lemma lem5160919 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term463 _67458 x _67457 _67459) = (term465 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160915 x _67457 _67458) (@lem5160918 x _67457 _67459)). Qed.
Lemma lem5160920 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term462 _67458 x _67457 _67459) = (term465 _67458 x _67457 _67459).
Proof. exact (TRANS (@lem5160910 _67458 x _67457 _67459) (@lem5160919 _67458 x _67457 _67459)). Qed.
Lemma lem5160921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5160922 (_67458 : real) (x : type1021) (_67457 : real -> Prop) (_67459 : real) : (term466 _67458 x _67457 _67459) = (term467 _67458 x _67457 _67459).
Proof. exact (MK_COMB (@lem5160921) (@lem5160920 _67458 x _67457 _67459)). Qed.
Lemma lem5160923 (_67457 : real -> Prop) : (_67457 = (@EMPTY real)) = (_67457 = (@EMPTY real)).
Proof. exact (eq_refl (_67457 = (@EMPTY real))). Qed.
Lemma lem5160924 (_67458 : real) (x : type1021) (_67459 : real) (_67457 : real -> Prop) : (term460 _67458 x _67459 _67457) = (term468 _67458 x _67459 _67457).
Proof. exact (MK_COMB (@lem5160922 _67458 x _67457 _67459) (@lem5160923 _67457)). Qed.
Lemma lem5160925 (_67458 : real) (x : type1021) (_67459 : real) (_67457 : real -> Prop) : (term386 _67458 x _67457 _67459) = (term468 _67458 x _67459 _67457).
Proof. exact (TRANS (@lem5160907 _67458 x _67459 _67457) (@lem5160924 _67458 x _67459 _67457)). Qed.
Lemma lem5160927 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term411 x s b.
Proof. exact (conj (@lem5160897 x s b h1 h2 h3) (@lem5160904 s b h3)). Qed.
Lemma lem5160928 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : term469 x s b.
Proof. exact (conj (@lem5160620 x s b h1 h2 h3) (@lem5160927 x s b h1 h2 h3)). Qed.
Lemma lem5160930 (_67458 : real) (_67459 : real) (_67457 : real -> Prop) (x : type1021) (h1 : term254 x) : term468 _67458 x _67459 _67457.
Proof. exact (EQ_MP (@lem5160925 _67458 x _67459 _67457) (@lem5160328 _67458 _67457 _67459 x h1)). Qed.
Lemma lem5160931 (b : real) (s : real -> Prop) (x : type1021) (h1 : term254 x) : term470 x b s.
Proof. exact (@lem5160930 b b s x h1). Qed.
Lemma lem5160934 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term90 s) (h3 : term56 s b) : s = (@EMPTY real).
Proof. exact (@lem5160931 b s x h1 (@lem5160928 x s b h1 h2 h3)). Qed.
Lemma lem5160935 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : term471 s.
Proof. exact (fun h0 : term90 s => @lem5160934 x s b h1 h0 h2). Qed.
Lemma lem5160937 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5160938 (s : real -> Prop) : (term471 s) = (s = (@EMPTY real)).
Proof. exact (@lem5160937 (s = (@EMPTY real))). Qed.
Lemma lem5160939 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5160938 s) (@lem5160935 x s b h1 h2)). Qed.
Lemma lem5160942 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5160944 (s : real -> Prop) : (term90 s) = (term472 s).
Proof. exact (@lem5160942 (s = (@EMPTY real))). Qed.
Lemma lem5160947 (s : real -> Prop) (b : real) (h1 : term56 s b) : term472 s.
Proof. exact (EQ_MP (@lem5160944 s) (@lem5160258 s b h1)). Qed.
Lemma lem5160950 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : False.
Proof. exact (@lem5160947 s b h2 (@lem5160939 x s b h1 h2)). Qed.
Lemma lem5160951 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : term473.
Proof. exact (fun h0 : ~ False => @lem5160950 x s b h1 h2). Qed.
Lemma lem5160953 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5160954 : term473 = False.
Proof. exact (@lem5160953 False). Qed.
Lemma lem5160955 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : False.
Proof. exact (EQ_MP (@lem5160954) (@lem5160951 x s b h1 h2)). Qed.
Lemma lem5160956 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : (term56 s b) = False.
Proof. exact (prop_ext (fun h3 : term56 s b => @lem5160955 x s b h1 h2) (fun h3 : False => @lem5160001 s b h2)). Qed.
Lemma lem5160957 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : False.
Proof. exact (EQ_MP (@lem5160956 x s b h1 h2) (@lem5160001 s b h2)). Qed.
Lemma lem5160958 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : (term254 x) = False.
Proof. exact (prop_ext (fun h3 : term254 x => @lem5160957 x s b h1 h2) (fun h3 : False => @lem5159960 x h1)). Qed.
Lemma lem5160959 (x : type1021) (s : real -> Prop) (b : real) (h1 : term254 x) (h2 : term56 s b) : False.
Proof. exact (EQ_MP (@lem5160958 x s b h1 h2) (@lem5159960 x h1)). Qed.
Lemma lem5160960 (x : type1021) (s : real -> Prop) (h1 : term254 x) (h2 : term10 s) : False.
Proof. exact (ex_elim (@lem5159329 s h2) (fun b : real => fun h0 : term64 s b => @lem5160959 x s b h1 h0)). Qed.
Lemma lem5160961 (s : real -> Prop) (h1 : term17) (h2 : term10 s) : False.
Proof. exact (ex_elim (@lem5159858 h1) (fun x : type1021 => fun h0 : term256 x => @lem5160960 x s h0 h2)). Qed.
Lemma lem5160962 (s : real -> Prop) (h1 : term10 s) : term15.
Proof. exact (fun h0 : term17 => @lem5160961 s h0 h1). Qed.
Lemma lem5160963 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5160964 (s : real -> Prop) (h1 : term10 s) : term16.
Proof. exact (EQ_MP (@lem5160963) (@lem5160962 s h1)). Qed.
Lemma lem5160965 (s : real -> Prop) : term19 s.
Proof. exact (fun h0 : term10 s => @lem5160964 s h0). Qed.
Lemma lem5160970 : term23.
Proof. exact (fun s : real -> Prop => @lem5160965 s). Qed.
Lemma lem5160971 : term22.
Proof. exact (EQ_MP (@lem5159196) (@lem5160970)). Qed.
Lemma lem5160972 (s : real -> Prop) : term474 s.
Proof. exact (@lem5160971 s). Qed.
Lemma lem5160973 (s : real -> Prop) : (term474 s) = (term11 s).
Proof. exact (eq_refl (term474 s)). Qed.
Lemma lem5160974 (s : real -> Prop) : term11 s.
Proof. exact (EQ_MP (@lem5160973 s) (@lem5160972 s)). Qed.
Lemma lem5160976 (s : real -> Prop) : term11 s.
Proof. exact (@lem5158960 s (@lem5160974 s)). Qed.
Lemma lem5160977 (s : real -> Prop) (h1 : term10 s) : term15.
Proof. exact (@lem5160976 s (@lem5158945 s h1)). Qed.
Lemma lem5160978 (s : real -> Prop) (h1 : term10 s) : False.
Proof. exact (@lem5160977 s h1 (@lem5136700)). Qed.
Lemma lem5160979 (s : real -> Prop) (h1 : term10 s) : (term10 s) = False.
Proof. exact (prop_ext (fun h2 : term10 s => @lem5160978 s h1) (fun h2 : False => @lem5158945 s h1)). Qed.
Lemma lem5160980 (s : real -> Prop) (h1 : term10 s) : False.
Proof. exact (EQ_MP (@lem5160979 s h1) (@lem5158945 s h1)). Qed.
Lemma lem5160981 (s : real -> Prop) : term9 s.
Proof. exact (fun h0 : term10 s => @lem5160980 s h0). Qed.
Lemma lem5160982 (s : real -> Prop) : term8 s.
Proof. exact (EQ_MP (@lem5158944 s) (@lem5160981 s)). Qed.
