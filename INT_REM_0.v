Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_0_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm2387577_spec.
Require Import thm69_spec.
Lemma lem2395879 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2395880 : term1 = term2.
Proof. exact (@lem2395879 term1). Qed.
Lemma lem2395881 : term2 = term1.
Proof. exact (SYM (@lem2395880)). Qed.
Lemma lem2395882 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2395885 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2395886 : term5.
Proof. exact (fun h0 : term4 => @lem2395885 h0). Qed.
Lemma lem2395887 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2395888 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2395889 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2395887 h2 (@lem2395888 h1)). Qed.
Lemma lem2395890 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2395889 h1 h0). Qed.
Lemma lem2395891 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2395892 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2395890 h1 (@lem2395891 h2)). Qed.
Lemma lem2395893 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2395892 h0 h1). Qed.
Lemma lem2395894 : term7.
Proof. exact (fun h0 : term5 => @lem2395893 h0). Qed.
Lemma lem2395897 : term5.
Proof. exact (@lem2395894 (@lem2395886)). Qed.
Lemma lem2395905 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2395906 : term8 = term9.
Proof. exact (@lem2395905 term10). Qed.
Lemma lem2395921 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2395928 : term4 = term12.
Proof. exact (MK_COMB (@lem2395921) (@lem2395906)). Qed.
Lemma lem2395932 (n : int) (h1 : (n = term13) = False) : (n = term13) = False.
Proof. exact (h1). Qed.
Lemma lem2395933 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem2395934 (n : int) (h1 : (n = term13) = False) : (term14 n) = (@COND Prop False).
Proof. exact (MK_COMB (@lem2395933) (@lem2395932 n h1)). Qed.
Lemma lem2395941 (n : int) (m : int) : (term15 n m) = (term15 n m).
Proof. exact (eq_refl (term15 n m)). Qed.
Lemma lem2395942 (m : int) (n : int) (h1 : (n = term13) = False) : (term16 n m) = (term17 n m).
Proof. exact (MK_COMB (@lem2395934 n h1) (@lem2395941 n m)). Qed.
Lemma lem2395949 (m : int) (n : int) : (term18 m n) = (term18 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem2395950 (m : int) (n : int) (h1 : (n = term13) = False) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem2395942 m n h1) (@lem2395949 m n)). Qed.
Lemma lem2395952 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem2395953 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem2395952 Prop t1 t2). Qed.
Lemma lem2395954 (m : int) (n : int) : (term20 m n) = (term18 m n).
Proof. exact (@lem2395953 (term15 n m) (term18 m n)). Qed.
Lemma lem2395957 (m : int) (n : int) (h1 : (n = term13) = False) : (term19 m n) = (term18 m n).
Proof. exact (TRANS (@lem2395950 m n h1) (@lem2395954 m n)). Qed.
Lemma lem2395958 (m : int) (n : int) : term21 m n.
Proof. exact (fun h0 : (n = term13) = False => @lem2395957 m n h0). Qed.
Lemma lem2395960 (n : int) (h1 : (n = term13) = True) : (n = term13) = True.
Proof. exact (h1). Qed.
Lemma lem2395961 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem2395962 (n : int) (h1 : (n = term13) = True) : (term14 n) = (@COND Prop True).
Proof. exact (MK_COMB (@lem2395961) (@lem2395960 n h1)). Qed.
Lemma lem2395969 (n : int) (m : int) : (term15 n m) = (term15 n m).
Proof. exact (eq_refl (term15 n m)). Qed.
Lemma lem2395970 (m : int) (n : int) (h1 : (n = term13) = True) : (term16 n m) = (term22 n m).
Proof. exact (MK_COMB (@lem2395962 n h1) (@lem2395969 n m)). Qed.
Lemma lem2395977 (m : int) (n : int) : (term18 m n) = (term18 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem2395978 (m : int) (n : int) (h1 : (n = term13) = True) : (term19 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem2395970 m n h1) (@lem2395977 m n)). Qed.
Lemma lem2395980 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem2395981 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem2395980 Prop t2 t1). Qed.
Lemma lem2395982 (n : int) (m : int) : (term23 m n) = (term15 n m).
Proof. exact (@lem2395981 (term18 m n) (term15 n m)). Qed.
Lemma lem2395985 (m : int) (n : int) (h1 : (n = term13) = True) : (term19 m n) = (term15 n m).
Proof. exact (TRANS (@lem2395978 m n h1) (@lem2395982 n m)). Qed.
Lemma lem2395986 (n : int) (m : int) : term24 n m.
Proof. exact (fun h0 : (n = term13) = True => @lem2395985 m n h0). Qed.
Lemma lem2395987 (n : int) (m : int) : term25 n m.
Proof. exact (conj (@lem2395958 m n) (@lem2395986 n m)). Qed.
Lemma lem2395989 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term26 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem2395990 (m : int) (n : int) : term27 m n.
Proof. exact (@lem2395989 (term19 m n) (term15 n m) (n = term13) (term18 m n)). Qed.
Lemma lem2396035 (m : int) (n : int) : (term19 m n) = (term28 m n).
Proof. exact (@lem2395990 m n (@lem2395987 n m)). Qed.
Lemma lem2396036 (m : int) : (term29 m) = (term30 m).
Proof. exact (fun_ext (fun n : int => @lem2396035 m n)). Qed.
Lemma lem2396037 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396038 (m : int) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem2396037) (@lem2396036 m)). Qed.
Lemma lem2396039 : term33 = term34.
Proof. exact (fun_ext (fun m : int => @lem2396038 m)). Qed.
Lemma lem2396040 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396041 : term10 = term35.
Proof. exact (MK_COMB (@lem2396040) (@lem2396039)). Qed.
Lemma lem2396042 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2396043 : term9 = term36.
Proof. exact (MK_COMB (@lem2396042) (@lem2396041)). Qed.
Lemma lem2396044 (m : int) : ((term37 m) = m) = ((term37 m) = m).
Proof. exact (eq_refl ((term37 m) = m)). Qed.
Lemma lem2396045 : term38 = term38.
Proof. exact (fun_ext (fun m : int => @lem2396044 m)). Qed.
Lemma lem2396046 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396047 : term1 = term1.
Proof. exact (MK_COMB (@lem2396046) (@lem2396045)). Qed.
Lemma lem2396048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2396049 : term3 = term3.
Proof. exact (MK_COMB (@lem2396048) (@lem2396047)). Qed.
Lemma lem2396050 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2396051 : term11 = term11.
Proof. exact (MK_COMB (@lem2396050) (@lem2396049)). Qed.
Lemma lem2396052 : term12 = term39.
Proof. exact (MK_COMB (@lem2396051) (@lem2396043)). Qed.
Lemma lem2396087 : term4 = term39.
Proof. exact (TRANS (@lem2395928) (@lem2396052)). Qed.
Lemma lem2396088 : term39 = term4.
Proof. exact (SYM (@lem2396087)). Qed.
Lemma lem2396089 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2396090 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem2396092 (P : int -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2396093 : term3 = term42.
Proof. exact (@lem2396092 term38). Qed.
Lemma lem2396094 (m : int) : (term43 m) = ((term37 m) = m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem2396095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2396097 (m : int) : (term44 m) = (term45 m).
Proof. exact (MK_COMB (@lem2396095) (@lem2396094 m)). Qed.
Lemma lem2396098 : term46 = term47.
Proof. exact (fun_ext (fun m : int => @lem2396097 m)). Qed.
Lemma lem2396099 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2396100 : term42 = term48.
Proof. exact (MK_COMB (@lem2396099) (@lem2396098)). Qed.
Lemma lem2396109 : term3 = term48.
Proof. exact (TRANS (@lem2396093) (@lem2396100)). Qed.
Lemma lem2396110 (h1 : term3) : term48.
Proof. exact (EQ_MP (@lem2396109) (@lem2396089 h1)). Qed.
Lemma lem2396135 (m : int) (n : int) : (term28 m n) = (term28 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem2396136 (m : int) : (term30 m) = (term30 m).
Proof. exact (fun_ext (fun n : int => @lem2396135 m n)). Qed.
Lemma lem2396137 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396138 (m : int) : (term32 m) = (term32 m).
Proof. exact (MK_COMB (@lem2396137) (@lem2396136 m)). Qed.
Lemma lem2396139 : term34 = term34.
Proof. exact (fun_ext (fun m : int => @lem2396138 m)). Qed.
Lemma lem2396140 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396141 : term35 = term35.
Proof. exact (MK_COMB (@lem2396140) (@lem2396139)). Qed.
Lemma lem2396147 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2396148 (P : int -> Prop) (Q : int -> Prop) : (term51 P Q) = (term52 P Q).
Proof. exact (@lem2396147 int P Q). Qed.
Lemma lem2396149 (m : int) : (term53 m) = (term54 m).
Proof. exact (@lem2396148 (term55 m) (term56 m)). Qed.
Lemma lem2396150 (n : int) (m : int) : (term57 m n) = (term58 n m).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem2396151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2396152 (n : int) (m : int) : (term59 m n) = (term60 n m).
Proof. exact (MK_COMB (@lem2396151) (@lem2396150 n m)). Qed.
Lemma lem2396153 (m : int) (n : int) : (term61 m n) = (term62 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem2396154 (m : int) (n : int) : (term63 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem2396152 n m) (@lem2396153 m n)). Qed.
Lemma lem2396155 (m : int) : (term64 m) = (term30 m).
Proof. exact (fun_ext (fun n : int => @lem2396154 m n)). Qed.
Lemma lem2396156 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396157 (m : int) : (term53 m) = (term32 m).
Proof. exact (MK_COMB (@lem2396156) (@lem2396155 m)). Qed.
Lemma lem2396158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2396159 (m : int) : (term65 m) = (term66 m).
Proof. exact (MK_COMB (@lem2396158) (@lem2396157 m)). Qed.
Lemma lem2396160 (n : int) (m : int) : (term57 m n) = (term58 n m).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem2396161 (m : int) : (term67 m) = (term55 m).
Proof. exact (fun_ext (fun n : int => @lem2396160 n m)). Qed.
Lemma lem2396162 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396163 (m : int) : (term68 m) = (term69 m).
Proof. exact (MK_COMB (@lem2396162) (@lem2396161 m)). Qed.
Lemma lem2396164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2396165 (m : int) : (term70 m) = (term71 m).
Proof. exact (MK_COMB (@lem2396164) (@lem2396163 m)). Qed.
Lemma lem2396166 (m : int) (n : int) : (term61 m n) = (term62 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem2396167 (m : int) : (term72 m) = (term56 m).
Proof. exact (fun_ext (fun n : int => @lem2396166 m n)). Qed.
Lemma lem2396168 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396169 (m : int) : (term73 m) = (term74 m).
Proof. exact (MK_COMB (@lem2396168) (@lem2396167 m)). Qed.
Lemma lem2396170 (m : int) : (term54 m) = (term75 m).
Proof. exact (MK_COMB (@lem2396165 m) (@lem2396169 m)). Qed.
Lemma lem2396171 (m : int) : ((term53 m) = (term54 m)) = ((term32 m) = (term75 m)).
Proof. exact (MK_COMB (@lem2396159 m) (@lem2396170 m)). Qed.
Lemma lem2396172 (m : int) : (term32 m) = (term75 m).
Proof. exact (EQ_MP (@lem2396171 m) (@lem2396149 m)). Qed.
Lemma lem2396269 : term34 = term76.
Proof. exact (fun_ext (fun m : int => @lem2396172 m)). Qed.
Lemma lem2396270 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396271 : term35 = term77.
Proof. exact (MK_COMB (@lem2396270) (@lem2396269)). Qed.
Lemma lem2396273 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2396274 (P : int -> Prop) (Q : int -> Prop) : (term51 P Q) = (term52 P Q).
Proof. exact (@lem2396273 int P Q). Qed.
Lemma lem2396275 : term78 = term79.
Proof. exact (@lem2396274 term80 term81). Qed.
Lemma lem2396276 (m : int) : (term82 m) = (term69 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem2396277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2396278 (m : int) : (term83 m) = (term71 m).
Proof. exact (MK_COMB (@lem2396277) (@lem2396276 m)). Qed.
Lemma lem2396279 (m : int) : (term84 m) = (term74 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem2396280 (m : int) : (term85 m) = (term75 m).
Proof. exact (MK_COMB (@lem2396278 m) (@lem2396279 m)). Qed.
Lemma lem2396281 : term86 = term76.
Proof. exact (fun_ext (fun m : int => @lem2396280 m)). Qed.
Lemma lem2396282 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396283 : term78 = term77.
Proof. exact (MK_COMB (@lem2396282) (@lem2396281)). Qed.
Lemma lem2396284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2396285 : term87 = term88.
Proof. exact (MK_COMB (@lem2396284) (@lem2396283)). Qed.
Lemma lem2396286 (m : int) : (term82 m) = (term69 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem2396287 : term89 = term80.
Proof. exact (fun_ext (fun m : int => @lem2396286 m)). Qed.
Lemma lem2396288 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396289 : term90 = term91.
Proof. exact (MK_COMB (@lem2396288) (@lem2396287)). Qed.
Lemma lem2396290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2396291 : term92 = term93.
Proof. exact (MK_COMB (@lem2396290) (@lem2396289)). Qed.
Lemma lem2396292 (m : int) : (term84 m) = (term74 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem2396293 : term94 = term81.
Proof. exact (fun_ext (fun m : int => @lem2396292 m)). Qed.
Lemma lem2396294 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396295 : term95 = term96.
Proof. exact (MK_COMB (@lem2396294) (@lem2396293)). Qed.
Lemma lem2396296 : term79 = term97.
Proof. exact (MK_COMB (@lem2396291) (@lem2396295)). Qed.
Lemma lem2396297 : (term78 = term79) = (term77 = term97).
Proof. exact (MK_COMB (@lem2396285) (@lem2396296)). Qed.
Lemma lem2396298 : term77 = term97.
Proof. exact (EQ_MP (@lem2396297) (@lem2396275)). Qed.
Lemma lem2396405 : term35 = term97.
Proof. exact (TRANS (@lem2396271) (@lem2396298)). Qed.
Lemma lem2396406 : term35 = term97.
Proof. exact (TRANS (@lem2396141) (@lem2396405)). Qed.
Lemma lem2396407 (h1 : term35) : term97.
Proof. exact (EQ_MP (@lem2396406) (@lem2396090 h1)). Qed.
Lemma lem2396471 (m : int) (n : int) : (term62 m n) = (term62 m n).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem2396472 (m : int) : (term56 m) = (term56 m).
Proof. exact (fun_ext (fun n : int => @lem2396471 m n)). Qed.
Lemma lem2396473 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396474 (m : int) : (term74 m) = (term74 m).
Proof. exact (MK_COMB (@lem2396473) (@lem2396472 m)). Qed.
Lemma lem2396475 : term81 = term81.
Proof. exact (fun_ext (fun m : int => @lem2396474 m)). Qed.
Lemma lem2396476 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396477 : term96 = term96.
Proof. exact (MK_COMB (@lem2396476) (@lem2396475)). Qed.
Lemma lem2396516 (n : int) (m : int) : (term58 n m) = (term58 n m).
Proof. exact (eq_refl (term58 n m)). Qed.
Lemma lem2396517 (m : int) : (term55 m) = (term55 m).
Proof. exact (fun_ext (fun n : int => @lem2396516 n m)). Qed.
Lemma lem2396518 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396519 (m : int) : (term69 m) = (term69 m).
Proof. exact (MK_COMB (@lem2396518) (@lem2396517 m)). Qed.
Lemma lem2396520 : term80 = term80.
Proof. exact (fun_ext (fun m : int => @lem2396519 m)). Qed.
Lemma lem2396521 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396522 : term91 = term91.
Proof. exact (MK_COMB (@lem2396521) (@lem2396520)). Qed.
Lemma lem2396523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2396524 : term93 = term93.
Proof. exact (MK_COMB (@lem2396523) (@lem2396522)). Qed.
Lemma lem2396525 : term97 = term97.
Proof. exact (MK_COMB (@lem2396524) (@lem2396477)). Qed.
Lemma lem2396526 (h1 : term35) : term97.
Proof. exact (EQ_MP (@lem2396525) (@lem2396407 h1)). Qed.
Lemma lem2396542 (m : int) (h1 : term45 m) : term45 m.
Proof. exact (h1). Qed.
Lemma lem2396544 (h1 : term35) : term91.
Proof. exact (proj1 (@lem2396526 h1)). Qed.
Lemma lem2396548 (m : int) (h1 : term45 m) : term45 m.
Proof. exact (h1). Qed.
Lemma lem2396566 (n : int) (m : int) : (term58 n m) = (term98 n m).
Proof. exact (@lem19490 ((div m n) = term13) (term99 n) ((rem m n) = m)). Qed.
Lemma lem2396567 (m : int) : (term55 m) = (term100 m).
Proof. exact (fun_ext (fun n : int => @lem2396566 n m)). Qed.
Lemma lem2396568 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396569 (m : int) : (term69 m) = (term101 m).
Proof. exact (MK_COMB (@lem2396568) (@lem2396567 m)). Qed.
Lemma lem2396570 : term80 = term102.
Proof. exact (fun_ext (fun m : int => @lem2396569 m)). Qed.
Lemma lem2396571 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2396573 : term91 = term103.
Proof. exact (MK_COMB (@lem2396571) (@lem2396570)). Qed.
Lemma lem2396574 (h1 : term35) : term103.
Proof. exact (EQ_MP (@lem2396573) (@lem2396544 h1)). Qed.
Lemma lem2396611 (_29379 : int) (h1 : term35) : term104 _29379.
Proof. exact (@lem2396574 h1 _29379). Qed.
Lemma lem2396612 (_29379 : int) : (term104 _29379) = (term101 _29379).
Proof. exact (eq_refl (term104 _29379)). Qed.
Lemma lem2396613 (_29379 : int) (h1 : term35) : term101 _29379.
Proof. exact (EQ_MP (@lem2396612 _29379) (@lem2396611 _29379 h1)). Qed.
Lemma lem2396614 (_29379 : int) (_29380 : int) (h1 : term35) : term105 _29379 _29380.
Proof. exact (@lem2396613 _29379 h1 _29380). Qed.
Lemma lem2396615 (_29380 : int) (_29379 : int) : (term105 _29379 _29380) = (term98 _29380 _29379).
Proof. exact (eq_refl (term105 _29379 _29380)). Qed.
Lemma lem2396616 (_29380 : int) (_29379 : int) (h1 : term35) : term98 _29380 _29379.
Proof. exact (EQ_MP (@lem2396615 _29380 _29379) (@lem2396614 _29379 _29380 h1)). Qed.
Lemma lem2396630 (m : int) (h1 : term45 m) : term45 m.
Proof. exact (h1). Qed.
Lemma lem2396660 (_29380 : int) (_29379 : int) (h1 : term35) : term106 _29380 _29379.
Proof. exact (proj2 (@lem2396616 _29380 _29379 h1)). Qed.
Lemma lem2396788 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2396789 : term13 = term13.
Proof. exact (@lem2396788 term13). Qed.
Lemma lem2396790 : term107.
Proof. exact (fun h0 : term108 => @lem2396789). Qed.
Lemma lem2396792 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2396793 : term107 = (term13 = term13).
Proof. exact (@lem2396792 (term13 = term13)). Qed.
Lemma lem2396794 : term13 = term13.
Proof. exact (EQ_MP (@lem2396793) (@lem2396790)). Qed.
Lemma lem2396800 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2396801 (_29379 : int) (_29380 : int) : (term106 _29380 _29379) = (term110 _29379 _29380).
Proof. exact (@lem2396800 ((rem _29379 _29380) = _29379) (term99 _29380)). Qed.
Lemma lem2396811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2396812 (_29379 : int) (_29380 : int) : (term111 _29380 _29379) = (term112 _29379 _29380).
Proof. exact (MK_COMB (@lem2396811) (@lem2396801 _29379 _29380)). Qed.
Lemma lem2396822 (_29379 : int) (_29380 : int) : (term110 _29379 _29380) = (term110 _29379 _29380).
Proof. exact (eq_refl (term110 _29379 _29380)). Qed.
Lemma lem2396823 (_29379 : int) (_29380 : int) : ((term106 _29380 _29379) = (term110 _29379 _29380)) = ((term110 _29379 _29380) = (term110 _29379 _29380)).
Proof. exact (MK_COMB (@lem2396812 _29379 _29380) (@lem2396822 _29379 _29380)). Qed.
Lemma lem2396825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2396826 (x : Prop) : (x = x) = True.
Proof. exact (@lem2396825 Prop x). Qed.
Lemma lem2396827 (_29379 : int) (_29380 : int) : ((term110 _29379 _29380) = (term110 _29379 _29380)) = True.
Proof. exact (@lem2396826 (term110 _29379 _29380)). Qed.
Lemma lem2396828 (_29379 : int) (_29380 : int) : ((term106 _29380 _29379) = (term110 _29379 _29380)) = True.
Proof. exact (TRANS (@lem2396823 _29379 _29380) (@lem2396827 _29379 _29380)). Qed.
Lemma lem2396829 (_29379 : int) (_29380 : int) : True = ((term106 _29380 _29379) = (term110 _29379 _29380)).
Proof. exact (SYM (@lem2396828 _29379 _29380)). Qed.
Lemma lem2396830 (_29379 : int) (_29380 : int) : (term106 _29380 _29379) = (term110 _29379 _29380).
Proof. exact (EQ_MP (@lem2396829 _29379 _29380) (@lem0)). Qed.
Lemma lem2396831 (_29379 : int) (_29380 : int) (h1 : term35) : term110 _29379 _29380.
Proof. exact (EQ_MP (@lem2396830 _29379 _29380) (@lem2396660 _29380 _29379 h1)). Qed.
Lemma lem2396833 (b : Prop) (a : Prop) : (a \/ b) = (term113 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2396834 (_29380 : int) (_29379 : int) : (term110 _29379 _29380) = (term114 _29380 _29379).
Proof. exact (@lem2396833 (term99 _29380) ((rem _29379 _29380) = _29379)). Qed.
Lemma lem2396836 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2396837 (_29380 : int) : (term116 _29380) = (_29380 = term13).
Proof. exact (@lem2396836 (_29380 = term13)). Qed.
Lemma lem2396838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2396839 (_29380 : int) : (term117 _29380) = (term118 _29380).
Proof. exact (MK_COMB (@lem2396838) (@lem2396837 _29380)). Qed.
Lemma lem2396840 (_29380 : int) (_29379 : int) : ((rem _29379 _29380) = _29379) = ((rem _29379 _29380) = _29379).
Proof. exact (eq_refl ((rem _29379 _29380) = _29379)). Qed.
Lemma lem2396841 (_29380 : int) (_29379 : int) : (term114 _29380 _29379) = (term119 _29380 _29379).
Proof. exact (MK_COMB (@lem2396839 _29380) (@lem2396840 _29380 _29379)). Qed.
Lemma lem2396842 (_29380 : int) (_29379 : int) : (term110 _29379 _29380) = (term119 _29380 _29379).
Proof. exact (TRANS (@lem2396834 _29380 _29379) (@lem2396841 _29380 _29379)). Qed.
Lemma lem2396845 (_29380 : int) (_29379 : int) (h1 : term35) : term119 _29380 _29379.
Proof. exact (EQ_MP (@lem2396842 _29380 _29379) (@lem2396831 _29379 _29380 h1)). Qed.
Lemma lem2396846 (_29379 : int) (h1 : term35) : term120 _29379.
Proof. exact (@lem2396845 term13 _29379 h1). Qed.
Lemma lem2396849 (_29379 : int) (h1 : term35) : (term37 _29379) = _29379.
Proof. exact (@lem2396846 _29379 h1 (@lem2396794)). Qed.
Lemma lem2396850 (m : int) (h1 : term35) : (term37 m) = m.
Proof. exact (@lem2396849 m h1). Qed.
Lemma lem2396851 (m : int) (h1 : term35) : term121 m.
Proof. exact (fun h0 : term45 m => @lem2396850 m h1). Qed.
Lemma lem2396853 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2396854 (m : int) : (term121 m) = ((term37 m) = m).
Proof. exact (@lem2396853 ((term37 m) = m)). Qed.
Lemma lem2396855 (m : int) (h1 : term35) : (term37 m) = m.
Proof. exact (EQ_MP (@lem2396854 m) (@lem2396851 m h1)). Qed.
Lemma lem2396858 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2396860 (m : int) : (term45 m) = (term122 m).
Proof. exact (@lem2396858 ((term37 m) = m)). Qed.
Lemma lem2396863 (m : int) (h1 : term45 m) : term122 m.
Proof. exact (EQ_MP (@lem2396860 m) (@lem2396630 m h1)). Qed.
Lemma lem2396866 (m : int) (h1 : term35) (h2 : term45 m) : False.
Proof. exact (@lem2396863 m h2 (@lem2396855 m h1)). Qed.
Lemma lem2396867 (m : int) (h1 : term35) (h2 : term45 m) : term123.
Proof. exact (fun h0 : ~ False => @lem2396866 m h1 h2). Qed.
Lemma lem2396869 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2396870 : term123 = False.
Proof. exact (@lem2396869 False). Qed.
Lemma lem2396871 (m : int) (h1 : term35) (h2 : term45 m) : False.
Proof. exact (EQ_MP (@lem2396870) (@lem2396867 m h1 h2)). Qed.
Lemma lem2396872 (m : int) (h1 : term35) (h2 : term45 m) : (term45 m) = False.
Proof. exact (prop_ext (fun h3 : term45 m => @lem2396871 m h1 h2) (fun h3 : False => @lem2396630 m h2)). Qed.
Lemma lem2396873 (m : int) (h1 : term35) (h2 : term45 m) : False.
Proof. exact (EQ_MP (@lem2396872 m h1 h2) (@lem2396630 m h2)). Qed.
Lemma lem2396874 (m : int) (h1 : term35) (h2 : term45 m) : (term45 m) = False.
Proof. exact (prop_ext (fun h3 : term45 m => @lem2396873 m h1 h2) (fun h3 : False => @lem2396548 m h2)). Qed.
Lemma lem2396875 (m : int) (h1 : term35) (h2 : term45 m) : False.
Proof. exact (EQ_MP (@lem2396874 m h1 h2) (@lem2396548 m h2)). Qed.
Lemma lem2396876 (m : int) (h1 : term35) (h2 : term45 m) : (term45 m) = False.
Proof. exact (prop_ext (fun h3 : term45 m => @lem2396875 m h1 h2) (fun h3 : False => @lem2396548 m h2)). Qed.
Lemma lem2396877 (m : int) (h1 : term35) (h2 : term45 m) : False.
Proof. exact (EQ_MP (@lem2396876 m h1 h2) (@lem2396548 m h2)). Qed.
Lemma lem2396878 (m : int) (h1 : term35) (h2 : term45 m) : (term45 m) = False.
Proof. exact (prop_ext (fun h3 : term45 m => @lem2396877 m h1 h2) (fun h3 : False => @lem2396542 m h2)). Qed.
Lemma lem2396879 (m : int) (h1 : term35) (h2 : term45 m) : False.
Proof. exact (EQ_MP (@lem2396878 m h1 h2) (@lem2396542 m h2)). Qed.
Lemma lem2396880 (h1 : term35) (h2 : term3) : False.
Proof. exact (ex_elim (@lem2396110 h2) (fun m : int => fun h0 : term47 m => @lem2396879 m h1 h0)). Qed.
Lemma lem2396881 (h1 : term3) : term124.
Proof. exact (fun h0 : term35 => @lem2396880 h0 h1). Qed.
Lemma lem2396882 : term124 = term36.
Proof. exact (@lem69 term35). Qed.
Lemma lem2396883 (h1 : term3) : term36.
Proof. exact (EQ_MP (@lem2396882) (@lem2396881 h1)). Qed.
Lemma lem2396884 : term39.
Proof. exact (fun h0 : term3 => @lem2396883 h0). Qed.
Lemma lem2396885 : term4.
Proof. exact (EQ_MP (@lem2396088) (@lem2396884)). Qed.
Lemma lem2396887 : term4.
Proof. exact (@lem2395897 (@lem2396885)). Qed.
Lemma lem2396888 (h1 : term3) : term8.
Proof. exact (@lem2396887 (@lem2395882 h1)). Qed.
Lemma lem2396889 (h1 : term3) : False.
Proof. exact (@lem2396888 h1 (@lem2387577)). Qed.
Lemma lem2396890 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2396889 h1) (fun h2 : False => @lem2395882 h1)). Qed.
Lemma lem2396891 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2396890 h1) (@lem2395882 h1)). Qed.
Lemma lem2396892 : term2.
Proof. exact (fun h0 : term3 => @lem2396891 h0). Qed.
Lemma lem2396893 : term1.
Proof. exact (EQ_MP (@lem2395881) (@lem2396892)). Qed.
