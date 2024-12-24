Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVISION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm155916_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem155928 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem155929 : term1 = term2.
Proof. exact (@lem155928 term1). Qed.
Lemma lem155930 : term2 = term1.
Proof. exact (SYM (@lem155929)). Qed.
Lemma lem155931 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem155934 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem155935 : term5.
Proof. exact (fun h0 : term4 => @lem155934 h0). Qed.
Lemma lem155936 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem155937 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem155938 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem155936 h2 (@lem155937 h1)). Qed.
Lemma lem155939 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem155938 h1 h0). Qed.
Lemma lem155940 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem155941 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem155939 h1 (@lem155940 h2)). Qed.
Lemma lem155942 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem155941 h0 h1). Qed.
Lemma lem155943 : term7.
Proof. exact (fun h0 : term5 => @lem155942 h0). Qed.
Lemma lem155946 : term5.
Proof. exact (@lem155943 (@lem155935)). Qed.
Lemma lem155962 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem155963 : term8 = term9.
Proof. exact (@lem155962 term10). Qed.
Lemma lem155976 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem155983 : term4 = term12.
Proof. exact (MK_COMB (@lem155976) (@lem155963)). Qed.
Lemma lem155987 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem155988 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem155989 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term13 n) = (@COND Prop False).
Proof. exact (MK_COMB (@lem155988) (@lem155987 n h1)). Qed.
Lemma lem155996 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem155997 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term15 n m) = (term16 n m).
Proof. exact (MK_COMB (@lem155989 n h1) (@lem155996 n m)). Qed.
Lemma lem156002 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem156003 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem155997 m n h1) (@lem156002 m n)). Qed.
Lemma lem156005 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem156006 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem156005 Prop t1 t2). Qed.
Lemma lem156007 (m : nat) (n : nat) : (term19 m n) = (term17 m n).
Proof. exact (@lem156006 (term14 n m) (term17 m n)). Qed.
Lemma lem156010 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term18 m n) = (term17 m n).
Proof. exact (TRANS (@lem156003 m n h1) (@lem156007 m n)). Qed.
Lemma lem156011 (m : nat) (n : nat) : term20 m n.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = False => @lem156010 m n h0). Qed.
Lemma lem156013 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem156014 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem156015 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term13 n) = (@COND Prop True).
Proof. exact (MK_COMB (@lem156014) (@lem156013 n h1)). Qed.
Lemma lem156022 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem156023 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term15 n m) = (term21 n m).
Proof. exact (MK_COMB (@lem156015 n h1) (@lem156022 n m)). Qed.
Lemma lem156028 (m : nat) (n : nat) : (term17 m n) = (term17 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem156029 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term18 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem156023 m n h1) (@lem156028 m n)). Qed.
Lemma lem156031 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem156032 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem156031 Prop t2 t1). Qed.
Lemma lem156033 (n : nat) (m : nat) : (term22 m n) = (term14 n m).
Proof. exact (@lem156032 (term17 m n) (term14 n m)). Qed.
Lemma lem156036 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term18 m n) = (term14 n m).
Proof. exact (TRANS (@lem156029 m n h1) (@lem156033 n m)). Qed.
Lemma lem156037 (n : nat) (m : nat) : term23 n m.
Proof. exact (fun h0 : (n = (NUMERAL 0)) = True => @lem156036 m n h0). Qed.
Lemma lem156038 (n : nat) (m : nat) : term24 n m.
Proof. exact (conj (@lem156011 m n) (@lem156037 n m)). Qed.
Lemma lem156040 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term25 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem156041 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem156040 (term18 m n) (term14 n m) (n = (NUMERAL 0)) (term17 m n)). Qed.
Lemma lem156082 (m : nat) (n : nat) : (term18 m n) = (term27 m n).
Proof. exact (@lem156041 m n (@lem156038 n m)). Qed.
Lemma lem156083 (m : nat) : (term28 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem156082 m n)). Qed.
Lemma lem156084 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156085 (m : nat) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem156084) (@lem156083 m)). Qed.
Lemma lem156086 : term32 = term33.
Proof. exact (fun_ext (fun m : nat => @lem156085 m)). Qed.
Lemma lem156087 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156088 : term10 = term34.
Proof. exact (MK_COMB (@lem156087) (@lem156086)). Qed.
Lemma lem156089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem156090 : term9 = term35.
Proof. exact (MK_COMB (@lem156089) (@lem156088)). Qed.
Lemma lem156101 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem156102 (m : nat) : (term37 m) = (term37 m).
Proof. exact (fun_ext (fun n : nat => @lem156101 m n)). Qed.
Lemma lem156103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156104 (m : nat) : (term38 m) = (term38 m).
Proof. exact (MK_COMB (@lem156103) (@lem156102 m)). Qed.
Lemma lem156105 : term39 = term39.
Proof. exact (fun_ext (fun m : nat => @lem156104 m)). Qed.
Lemma lem156106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156107 : term1 = term1.
Proof. exact (MK_COMB (@lem156106) (@lem156105)). Qed.
Lemma lem156108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem156109 : term3 = term3.
Proof. exact (MK_COMB (@lem156108) (@lem156107)). Qed.
Lemma lem156110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem156111 : term11 = term11.
Proof. exact (MK_COMB (@lem156110) (@lem156109)). Qed.
Lemma lem156112 : term12 = term40.
Proof. exact (MK_COMB (@lem156111) (@lem156090)). Qed.
Lemma lem156155 : term4 = term40.
Proof. exact (TRANS (@lem155983) (@lem156112)). Qed.
Lemma lem156156 : term40 = term4.
Proof. exact (SYM (@lem156155)). Qed.
Lemma lem156157 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem156158 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem156166 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (@lem17045 (m = (term43 m n)) (term44 m n)). Qed.
Lemma lem156168 (n : nat) : (term45 n) = (term45 n).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem156169 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem156168 n) (@lem156166 m n)). Qed.
Lemma lem156170 (m : nat) (n : nat) : (term48 m n) = (term46 m n).
Proof. exact (@lem17362 (term49 n) (term17 m n)). Qed.
Lemma lem156171 (m : nat) (n : nat) : (term48 m n) = (term47 m n).
Proof. exact (TRANS (@lem156170 m n) (@lem156169 m n)). Qed.
Lemma lem156172 (P : nat -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem156173 (m : nat) : (term52 m) = (term53 m).
Proof. exact (@lem156172 (term37 m)). Qed.
Lemma lem156174 (m : nat) (n : nat) : (term54 m n) = (term36 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem156175 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem156176 (m : nat) (n : nat) : (term55 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem156175) (@lem156174 m n)). Qed.
Lemma lem156177 (m : nat) (n : nat) : (term55 m n) = (term47 m n).
Proof. exact (TRANS (@lem156176 m n) (@lem156171 m n)). Qed.
Lemma lem156178 (m : nat) : (term56 m) = (term57 m).
Proof. exact (fun_ext (fun n : nat => @lem156177 m n)). Qed.
Lemma lem156179 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem156180 (m : nat) : (term53 m) = (term58 m).
Proof. exact (MK_COMB (@lem156179) (@lem156178 m)). Qed.
Lemma lem156181 (m : nat) : (term52 m) = (term58 m).
Proof. exact (TRANS (@lem156173 m) (@lem156180 m)). Qed.
Lemma lem156182 (P : nat -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem156183 : term3 = term59.
Proof. exact (@lem156182 term39). Qed.
Lemma lem156184 (m : nat) : (term60 m) = (term38 m).
Proof. exact (eq_refl (term60 m)). Qed.
Lemma lem156185 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem156186 (m : nat) : (term61 m) = (term52 m).
Proof. exact (MK_COMB (@lem156185) (@lem156184 m)). Qed.
Lemma lem156187 (m : nat) : (term61 m) = (term58 m).
Proof. exact (TRANS (@lem156186 m) (@lem156181 m)). Qed.
Lemma lem156188 : term62 = term63.
Proof. exact (fun_ext (fun m : nat => @lem156187 m)). Qed.
Lemma lem156189 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem156190 : term59 = term64.
Proof. exact (MK_COMB (@lem156189) (@lem156188)). Qed.
Lemma lem156247 : term3 = term64.
Proof. exact (TRANS (@lem156183) (@lem156190)). Qed.
Lemma lem156248 (h1 : term3) : term64.
Proof. exact (EQ_MP (@lem156247) (@lem156157 h1)). Qed.
Lemma lem156269 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem156270 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem156269 m n)). Qed.
Lemma lem156271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156272 (m : nat) : (term31 m) = (term31 m).
Proof. exact (MK_COMB (@lem156271) (@lem156270 m)). Qed.
Lemma lem156273 : term33 = term33.
Proof. exact (fun_ext (fun m : nat => @lem156272 m)). Qed.
Lemma lem156274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156275 : term34 = term34.
Proof. exact (MK_COMB (@lem156274) (@lem156273)). Qed.
Lemma lem156281 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term65 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem156282 (P : nat -> Prop) (Q : nat -> Prop) : (term67 P Q) = (term68 P Q).
Proof. exact (@lem156281 nat P Q). Qed.
Lemma lem156283 (m : nat) : (term69 m) = (term70 m).
Proof. exact (@lem156282 (term71 m) (term72 m)). Qed.
Lemma lem156284 (n : nat) (m : nat) : (term73 m n) = (term74 n m).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem156285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem156286 (n : nat) (m : nat) : (term75 m n) = (term76 n m).
Proof. exact (MK_COMB (@lem156285) (@lem156284 n m)). Qed.
Lemma lem156287 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (eq_refl (term77 m n)). Qed.
Lemma lem156288 (m : nat) (n : nat) : (term79 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem156286 n m) (@lem156287 m n)). Qed.
Lemma lem156289 (m : nat) : (term80 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem156288 m n)). Qed.
Lemma lem156290 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156291 (m : nat) : (term69 m) = (term31 m).
Proof. exact (MK_COMB (@lem156290) (@lem156289 m)). Qed.
Lemma lem156292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem156293 (m : nat) : (term81 m) = (term82 m).
Proof. exact (MK_COMB (@lem156292) (@lem156291 m)). Qed.
Lemma lem156294 (n : nat) (m : nat) : (term73 m n) = (term74 n m).
Proof. exact (eq_refl (term73 m n)). Qed.
Lemma lem156295 (m : nat) : (term83 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem156294 n m)). Qed.
Lemma lem156296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156297 (m : nat) : (term84 m) = (term85 m).
Proof. exact (MK_COMB (@lem156296) (@lem156295 m)). Qed.
Lemma lem156298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem156299 (m : nat) : (term86 m) = (term87 m).
Proof. exact (MK_COMB (@lem156298) (@lem156297 m)). Qed.
Lemma lem156300 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (eq_refl (term77 m n)). Qed.
Lemma lem156301 (m : nat) : (term88 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem156300 m n)). Qed.
Lemma lem156302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156303 (m : nat) : (term89 m) = (term90 m).
Proof. exact (MK_COMB (@lem156302) (@lem156301 m)). Qed.
Lemma lem156304 (m : nat) : (term70 m) = (term91 m).
Proof. exact (MK_COMB (@lem156299 m) (@lem156303 m)). Qed.
Lemma lem156305 (m : nat) : ((term69 m) = (term70 m)) = ((term31 m) = (term91 m)).
Proof. exact (MK_COMB (@lem156293 m) (@lem156304 m)). Qed.
Lemma lem156306 (m : nat) : (term31 m) = (term91 m).
Proof. exact (EQ_MP (@lem156305 m) (@lem156283 m)). Qed.
Lemma lem156403 : term33 = term92.
Proof. exact (fun_ext (fun m : nat => @lem156306 m)). Qed.
Lemma lem156404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156405 : term34 = term93.
Proof. exact (MK_COMB (@lem156404) (@lem156403)). Qed.
Lemma lem156407 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term65 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem156408 (P : nat -> Prop) (Q : nat -> Prop) : (term67 P Q) = (term68 P Q).
Proof. exact (@lem156407 nat P Q). Qed.
Lemma lem156409 : term94 = term95.
Proof. exact (@lem156408 term96 term97). Qed.
Lemma lem156410 (m : nat) : (term98 m) = (term85 m).
Proof. exact (eq_refl (term98 m)). Qed.
Lemma lem156411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem156412 (m : nat) : (term99 m) = (term87 m).
Proof. exact (MK_COMB (@lem156411) (@lem156410 m)). Qed.
Lemma lem156413 (m : nat) : (term100 m) = (term90 m).
Proof. exact (eq_refl (term100 m)). Qed.
Lemma lem156414 (m : nat) : (term101 m) = (term91 m).
Proof. exact (MK_COMB (@lem156412 m) (@lem156413 m)). Qed.
Lemma lem156415 : term102 = term92.
Proof. exact (fun_ext (fun m : nat => @lem156414 m)). Qed.
Lemma lem156416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156417 : term94 = term93.
Proof. exact (MK_COMB (@lem156416) (@lem156415)). Qed.
Lemma lem156418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem156419 : term103 = term104.
Proof. exact (MK_COMB (@lem156418) (@lem156417)). Qed.
Lemma lem156420 (m : nat) : (term98 m) = (term85 m).
Proof. exact (eq_refl (term98 m)). Qed.
Lemma lem156421 : term105 = term96.
Proof. exact (fun_ext (fun m : nat => @lem156420 m)). Qed.
Lemma lem156422 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156423 : term106 = term107.
Proof. exact (MK_COMB (@lem156422) (@lem156421)). Qed.
Lemma lem156424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem156425 : term108 = term109.
Proof. exact (MK_COMB (@lem156424) (@lem156423)). Qed.
Lemma lem156426 (m : nat) : (term100 m) = (term90 m).
Proof. exact (eq_refl (term100 m)). Qed.
Lemma lem156427 : term110 = term97.
Proof. exact (fun_ext (fun m : nat => @lem156426 m)). Qed.
Lemma lem156428 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156429 : term111 = term112.
Proof. exact (MK_COMB (@lem156428) (@lem156427)). Qed.
Lemma lem156430 : term95 = term113.
Proof. exact (MK_COMB (@lem156425) (@lem156429)). Qed.
Lemma lem156431 : (term94 = term95) = (term93 = term113).
Proof. exact (MK_COMB (@lem156419) (@lem156430)). Qed.
Lemma lem156432 : term93 = term113.
Proof. exact (EQ_MP (@lem156431) (@lem156409)). Qed.
Lemma lem156539 : term34 = term113.
Proof. exact (TRANS (@lem156405) (@lem156432)). Qed.
Lemma lem156540 : term34 = term113.
Proof. exact (TRANS (@lem156275) (@lem156539)). Qed.
Lemma lem156541 (h1 : term34) : term113.
Proof. exact (EQ_MP (@lem156540) (@lem156158 h1)). Qed.
Lemma lem156542 (m : nat) (h1 : term58 m) : term58 m.
Proof. exact (h1). Qed.
Lemma lem156586 (m : nat) (n : nat) : (term78 m n) = (term78 m n).
Proof. exact (eq_refl (term78 m n)). Qed.
Lemma lem156587 (m : nat) : (term72 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem156586 m n)). Qed.
Lemma lem156588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156589 (m : nat) : (term90 m) = (term90 m).
Proof. exact (MK_COMB (@lem156588) (@lem156587 m)). Qed.
Lemma lem156590 : term97 = term97.
Proof. exact (fun_ext (fun m : nat => @lem156589 m)). Qed.
Lemma lem156591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156592 : term112 = term112.
Proof. exact (MK_COMB (@lem156591) (@lem156590)). Qed.
Lemma lem156627 (n : nat) (m : nat) : (term74 n m) = (term74 n m).
Proof. exact (eq_refl (term74 n m)). Qed.
Lemma lem156628 (m : nat) : (term71 m) = (term71 m).
Proof. exact (fun_ext (fun n : nat => @lem156627 n m)). Qed.
Lemma lem156629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156630 (m : nat) : (term85 m) = (term85 m).
Proof. exact (MK_COMB (@lem156629) (@lem156628 m)). Qed.
Lemma lem156631 : term96 = term96.
Proof. exact (fun_ext (fun m : nat => @lem156630 m)). Qed.
Lemma lem156632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156633 : term107 = term107.
Proof. exact (MK_COMB (@lem156632) (@lem156631)). Qed.
Lemma lem156634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem156635 : term109 = term109.
Proof. exact (MK_COMB (@lem156634) (@lem156633)). Qed.
Lemma lem156636 : term113 = term113.
Proof. exact (MK_COMB (@lem156635) (@lem156592)). Qed.
Lemma lem156637 (h1 : term34) : term113.
Proof. exact (EQ_MP (@lem156636) (@lem156541 h1)). Qed.
Lemma lem156687 (m : nat) (n : nat) (h1 : term47 m n) : term47 m n.
Proof. exact (h1). Qed.
Lemma lem156688 (m : nat) (n : nat) (h1 : term47 m n) : term42 m n.
Proof. exact (proj2 (@lem156687 m n h1)). Qed.
Lemma lem156690 (h1 : term34) : term112.
Proof. exact (proj2 (@lem156637 h1)). Qed.
Lemma lem156741 (m : nat) (n : nat) : (term78 m n) = (term114 m n).
Proof. exact (@lem19490 (m = (term43 m n)) (n = (NUMERAL 0)) (term44 m n)). Qed.
Lemma lem156742 (m : nat) : (term72 m) = (term115 m).
Proof. exact (fun_ext (fun n : nat => @lem156741 m n)). Qed.
Lemma lem156743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156744 (m : nat) : (term90 m) = (term116 m).
Proof. exact (MK_COMB (@lem156743) (@lem156742 m)). Qed.
Lemma lem156745 : term97 = term117.
Proof. exact (fun_ext (fun m : nat => @lem156744 m)). Qed.
Lemma lem156746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156748 : term112 = term118.
Proof. exact (MK_COMB (@lem156746) (@lem156745)). Qed.
Lemma lem156749 (h1 : term34) : term118.
Proof. exact (EQ_MP (@lem156748) (@lem156690 h1)). Qed.
Lemma lem156753 (m : nat) (n : nat) (h1 : term119 m n) : term119 m n.
Proof. exact (h1). Qed.
Lemma lem156801 (m : nat) (n : nat) : (term78 m n) = (term114 m n).
Proof. exact (@lem19490 (m = (term43 m n)) (n = (NUMERAL 0)) (term44 m n)). Qed.
Lemma lem156802 (m : nat) : (term72 m) = (term115 m).
Proof. exact (fun_ext (fun n : nat => @lem156801 m n)). Qed.
Lemma lem156803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156804 (m : nat) : (term90 m) = (term116 m).
Proof. exact (MK_COMB (@lem156803) (@lem156802 m)). Qed.
Lemma lem156805 : term97 = term117.
Proof. exact (fun_ext (fun m : nat => @lem156804 m)). Qed.
Lemma lem156806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem156808 : term112 = term118.
Proof. exact (MK_COMB (@lem156806) (@lem156805)). Qed.
Lemma lem156809 (h1 : term34) : term118.
Proof. exact (EQ_MP (@lem156808) (@lem156690 h1)). Qed.
Lemma lem156813 (m : nat) (n : nat) (h1 : term120 m n) : term120 m n.
Proof. exact (h1). Qed.
Lemma lem156820 (_3090 : nat) (h1 : term34) : term121 _3090.
Proof. exact (@lem156749 h1 _3090). Qed.
Lemma lem156821 (_3090 : nat) : (term121 _3090) = (term116 _3090).
Proof. exact (eq_refl (term121 _3090)). Qed.
Lemma lem156822 (_3090 : nat) (h1 : term34) : term116 _3090.
Proof. exact (EQ_MP (@lem156821 _3090) (@lem156820 _3090 h1)). Qed.
Lemma lem156823 (_3090 : nat) (_3091 : nat) (h1 : term34) : term122 _3090 _3091.
Proof. exact (@lem156822 _3090 h1 _3091). Qed.
Lemma lem156824 (_3090 : nat) (_3091 : nat) : (term122 _3090 _3091) = (term114 _3090 _3091).
Proof. exact (eq_refl (term122 _3090 _3091)). Qed.
Lemma lem156825 (_3090 : nat) (_3091 : nat) (h1 : term34) : term114 _3090 _3091.
Proof. exact (EQ_MP (@lem156824 _3090 _3091) (@lem156823 _3090 _3091 h1)). Qed.
Lemma lem156832 (_3094 : nat) (h1 : term34) : term121 _3094.
Proof. exact (@lem156809 h1 _3094). Qed.
Lemma lem156833 (_3094 : nat) : (term121 _3094) = (term116 _3094).
Proof. exact (eq_refl (term121 _3094)). Qed.
Lemma lem156834 (_3094 : nat) (h1 : term34) : term116 _3094.
Proof. exact (EQ_MP (@lem156833 _3094) (@lem156832 _3094 h1)). Qed.
Lemma lem156835 (_3094 : nat) (_3095 : nat) (h1 : term34) : term122 _3094 _3095.
Proof. exact (@lem156834 _3094 h1 _3095). Qed.
Lemma lem156836 (_3094 : nat) (_3095 : nat) : (term122 _3094 _3095) = (term114 _3094 _3095).
Proof. exact (eq_refl (term122 _3094 _3095)). Qed.
Lemma lem156837 (_3094 : nat) (_3095 : nat) (h1 : term34) : term114 _3094 _3095.
Proof. exact (EQ_MP (@lem156836 _3094 _3095) (@lem156835 _3094 _3095 h1)). Qed.
Lemma lem156849 (m : nat) (n : nat) (h1 : term119 m n) : term119 m n.
Proof. exact (h1). Qed.
Lemma lem156855 (_3090 : nat) (_3091 : nat) (h1 : term34) : term123 _3090 _3091.
Proof. exact (proj1 (@lem156825 _3090 _3091 h1)). Qed.
Lemma lem156877 (m : nat) (n : nat) (h1 : term120 m n) : term120 m n.
Proof. exact (h1). Qed.
Lemma lem156889 (_3094 : nat) (_3095 : nat) (h1 : term34) : term124 _3094 _3095.
Proof. exact (proj2 (@lem156837 _3094 _3095 h1)). Qed.
Lemma lem156992 (m : nat) (n : nat) (h1 : term47 m n) : term49 n.
Proof. exact (proj1 (@lem156687 m n h1)). Qed.
Lemma lem156993 (m : nat) (n : nat) (h1 : term47 m n) : term125 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem156992 m n h1). Qed.
Lemma lem156995 (p : Prop) : (term126 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem156996 (n : nat) : (term125 n) = (term49 n).
Proof. exact (@lem156995 (n = (NUMERAL 0))). Qed.
Lemma lem156997 (m : nat) (n : nat) (h1 : term47 m n) : term49 n.
Proof. exact (EQ_MP (@lem156996 n) (@lem156993 m n h1)). Qed.
Lemma lem157003 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem157004 (_3090 : nat) (_3091 : nat) : (term123 _3090 _3091) = (term127 _3090 _3091).
Proof. exact (@lem157003 (_3090 = (term43 _3090 _3091)) (_3091 = (NUMERAL 0))). Qed.
Lemma lem157014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem157015 (_3090 : nat) (_3091 : nat) : (term128 _3090 _3091) = (term129 _3090 _3091).
Proof. exact (MK_COMB (@lem157014) (@lem157004 _3090 _3091)). Qed.
Lemma lem157025 (_3090 : nat) (_3091 : nat) : (term127 _3090 _3091) = (term127 _3090 _3091).
Proof. exact (eq_refl (term127 _3090 _3091)). Qed.
Lemma lem157026 (_3090 : nat) (_3091 : nat) : ((term123 _3090 _3091) = (term127 _3090 _3091)) = ((term127 _3090 _3091) = (term127 _3090 _3091)).
Proof. exact (MK_COMB (@lem157015 _3090 _3091) (@lem157025 _3090 _3091)). Qed.
Lemma lem157028 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem157029 (x : Prop) : (x = x) = True.
Proof. exact (@lem157028 Prop x). Qed.
Lemma lem157030 (_3090 : nat) (_3091 : nat) : ((term127 _3090 _3091) = (term127 _3090 _3091)) = True.
Proof. exact (@lem157029 (term127 _3090 _3091)). Qed.
Lemma lem157031 (_3090 : nat) (_3091 : nat) : ((term123 _3090 _3091) = (term127 _3090 _3091)) = True.
Proof. exact (TRANS (@lem157026 _3090 _3091) (@lem157030 _3090 _3091)). Qed.
Lemma lem157032 (_3090 : nat) (_3091 : nat) : True = ((term123 _3090 _3091) = (term127 _3090 _3091)).
Proof. exact (SYM (@lem157031 _3090 _3091)). Qed.
Lemma lem157033 (_3090 : nat) (_3091 : nat) : (term123 _3090 _3091) = (term127 _3090 _3091).
Proof. exact (EQ_MP (@lem157032 _3090 _3091) (@lem0)). Qed.
Lemma lem157034 (_3090 : nat) (_3091 : nat) (h1 : term34) : term127 _3090 _3091.
Proof. exact (EQ_MP (@lem157033 _3090 _3091) (@lem156855 _3090 _3091 h1)). Qed.
Lemma lem157036 (b : Prop) (a : Prop) : (a \/ b) = (term130 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem157039 (_3090 : nat) (_3091 : nat) : (term127 _3090 _3091) = (term131 _3090 _3091).
Proof. exact (@lem157036 (_3091 = (NUMERAL 0)) (_3090 = (term43 _3090 _3091))). Qed.
Lemma lem157042 (_3090 : nat) (_3091 : nat) (h1 : term34) : term131 _3090 _3091.
Proof. exact (EQ_MP (@lem157039 _3090 _3091) (@lem157034 _3090 _3091 h1)). Qed.
Lemma lem157043 (_3090 : nat) (n : nat) (h1 : term34) : term131 _3090 n.
Proof. exact (@lem157042 _3090 n h1). Qed.
Lemma lem157046 (_3090 : nat) (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : _3090 = (term43 _3090 n).
Proof. exact (@lem157043 _3090 n h1 (@lem156997 m n h2)). Qed.
Lemma lem157047 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : m = (term43 m n).
Proof. exact (@lem157046 m m n h1 h2). Qed.
Lemma lem157048 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : term132 m n.
Proof. exact (fun h0 : term119 m n => @lem157047 m n h1 h2). Qed.
Lemma lem157050 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem157051 (m : nat) (n : nat) : (term132 m n) = (m = (term43 m n)).
Proof. exact (@lem157050 (m = (term43 m n))). Qed.
Lemma lem157052 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : m = (term43 m n).
Proof. exact (EQ_MP (@lem157051 m n) (@lem157048 m n h1 h2)). Qed.
Lemma lem157055 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem157057 (m : nat) (n : nat) : (term119 m n) = (term134 m n).
Proof. exact (@lem157055 (m = (term43 m n))). Qed.
Lemma lem157060 (m : nat) (n : nat) (h1 : term119 m n) : term134 m n.
Proof. exact (EQ_MP (@lem157057 m n) (@lem156849 m n h1)). Qed.
Lemma lem157063 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : False.
Proof. exact (@lem157060 m n h2 (@lem157052 m n h1 h3)). Qed.
Lemma lem157064 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : term135.
Proof. exact (fun h0 : ~ False => @lem157063 m n h1 h2 h3). Qed.
Lemma lem157066 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem157067 : term135 = False.
Proof. exact (@lem157066 False). Qed.
Lemma lem157068 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157067) (@lem157064 m n h1 h2 h3)). Qed.
Lemma lem157159 (m : nat) (n : nat) (h1 : term47 m n) : term49 n.
Proof. exact (proj1 (@lem156687 m n h1)). Qed.
Lemma lem157160 (m : nat) (n : nat) (h1 : term47 m n) : term125 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem157159 m n h1). Qed.
Lemma lem157162 (p : Prop) : (term126 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem157163 (n : nat) : (term125 n) = (term49 n).
Proof. exact (@lem157162 (n = (NUMERAL 0))). Qed.
Lemma lem157164 (m : nat) (n : nat) (h1 : term47 m n) : term49 n.
Proof. exact (EQ_MP (@lem157163 n) (@lem157160 m n h1)). Qed.
Lemma lem157170 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem157171 (_3094 : nat) (_3095 : nat) : (term124 _3094 _3095) = (term136 _3094 _3095).
Proof. exact (@lem157170 (term44 _3094 _3095) (_3095 = (NUMERAL 0))). Qed.
Lemma lem157179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem157180 (_3094 : nat) (_3095 : nat) : (term137 _3094 _3095) = (term138 _3094 _3095).
Proof. exact (MK_COMB (@lem157179) (@lem157171 _3094 _3095)). Qed.
Lemma lem157188 (_3094 : nat) (_3095 : nat) : (term136 _3094 _3095) = (term136 _3094 _3095).
Proof. exact (eq_refl (term136 _3094 _3095)). Qed.
Lemma lem157189 (_3094 : nat) (_3095 : nat) : ((term124 _3094 _3095) = (term136 _3094 _3095)) = ((term136 _3094 _3095) = (term136 _3094 _3095)).
Proof. exact (MK_COMB (@lem157180 _3094 _3095) (@lem157188 _3094 _3095)). Qed.
Lemma lem157191 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem157192 (x : Prop) : (x = x) = True.
Proof. exact (@lem157191 Prop x). Qed.
Lemma lem157193 (_3094 : nat) (_3095 : nat) : ((term136 _3094 _3095) = (term136 _3094 _3095)) = True.
Proof. exact (@lem157192 (term136 _3094 _3095)). Qed.
Lemma lem157194 (_3094 : nat) (_3095 : nat) : ((term124 _3094 _3095) = (term136 _3094 _3095)) = True.
Proof. exact (TRANS (@lem157189 _3094 _3095) (@lem157193 _3094 _3095)). Qed.
Lemma lem157195 (_3094 : nat) (_3095 : nat) : True = ((term124 _3094 _3095) = (term136 _3094 _3095)).
Proof. exact (SYM (@lem157194 _3094 _3095)). Qed.
Lemma lem157196 (_3094 : nat) (_3095 : nat) : (term124 _3094 _3095) = (term136 _3094 _3095).
Proof. exact (EQ_MP (@lem157195 _3094 _3095) (@lem0)). Qed.
Lemma lem157197 (_3094 : nat) (_3095 : nat) (h1 : term34) : term136 _3094 _3095.
Proof. exact (EQ_MP (@lem157196 _3094 _3095) (@lem156889 _3094 _3095 h1)). Qed.
Lemma lem157199 (b : Prop) (a : Prop) : (a \/ b) = (term130 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem157202 (_3094 : nat) (_3095 : nat) : (term136 _3094 _3095) = (term139 _3094 _3095).
Proof. exact (@lem157199 (_3095 = (NUMERAL 0)) (term44 _3094 _3095)). Qed.
Lemma lem157205 (_3094 : nat) (_3095 : nat) (h1 : term34) : term139 _3094 _3095.
Proof. exact (EQ_MP (@lem157202 _3094 _3095) (@lem157197 _3094 _3095 h1)). Qed.
Lemma lem157206 (_3094 : nat) (n : nat) (h1 : term34) : term139 _3094 n.
Proof. exact (@lem157205 _3094 n h1). Qed.
Lemma lem157209 (_3094 : nat) (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : term44 _3094 n.
Proof. exact (@lem157206 _3094 n h1 (@lem157164 m n h2)). Qed.
Lemma lem157210 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : term44 m n.
Proof. exact (@lem157209 m m n h1 h2). Qed.
Lemma lem157211 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : term140 m n.
Proof. exact (fun h0 : term120 m n => @lem157210 m n h1 h2). Qed.
Lemma lem157213 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem157214 (m : nat) (n : nat) : (term140 m n) = (term44 m n).
Proof. exact (@lem157213 (term44 m n)). Qed.
Lemma lem157215 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : term44 m n.
Proof. exact (EQ_MP (@lem157214 m n) (@lem157211 m n h1 h2)). Qed.
Lemma lem157218 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem157220 (m : nat) (n : nat) : (term120 m n) = (term141 m n).
Proof. exact (@lem157218 (term44 m n)). Qed.
Lemma lem157223 (m : nat) (n : nat) (h1 : term120 m n) : term141 m n.
Proof. exact (EQ_MP (@lem157220 m n) (@lem156877 m n h1)). Qed.
Lemma lem157226 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : False.
Proof. exact (@lem157223 m n h2 (@lem157215 m n h1 h3)). Qed.
Lemma lem157227 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : term135.
Proof. exact (fun h0 : ~ False => @lem157226 m n h1 h2 h3). Qed.
Lemma lem157229 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem157230 : term135 = False.
Proof. exact (@lem157229 False). Qed.
Lemma lem157231 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157230) (@lem157227 m n h1 h2 h3)). Qed.
Lemma lem157232 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : (term120 m n) = False.
Proof. exact (prop_ext (fun h4 : term120 m n => @lem157231 m n h1 h2 h3) (fun h4 : False => @lem156877 m n h2)). Qed.
Lemma lem157233 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157232 m n h1 h2 h3) (@lem156877 m n h2)). Qed.
Lemma lem157234 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : (term119 m n) = False.
Proof. exact (prop_ext (fun h4 : term119 m n => @lem157068 m n h1 h2 h3) (fun h4 : False => @lem156849 m n h2)). Qed.
Lemma lem157235 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157234 m n h1 h2 h3) (@lem156849 m n h2)). Qed.
Lemma lem157236 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : (term120 m n) = False.
Proof. exact (prop_ext (fun h4 : term120 m n => @lem157233 m n h1 h2 h3) (fun h4 : False => @lem156813 m n h2)). Qed.
Lemma lem157237 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157236 m n h1 h2 h3) (@lem156813 m n h2)). Qed.
Lemma lem157238 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : (term119 m n) = False.
Proof. exact (prop_ext (fun h4 : term119 m n => @lem157235 m n h1 h2 h3) (fun h4 : False => @lem156753 m n h2)). Qed.
Lemma lem157239 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157238 m n h1 h2 h3) (@lem156753 m n h2)). Qed.
Lemma lem157240 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : (term120 m n) = False.
Proof. exact (prop_ext (fun h4 : term120 m n => @lem157237 m n h1 h2 h3) (fun h4 : False => @lem156813 m n h2)). Qed.
Lemma lem157241 (m : nat) (n : nat) (h1 : term34) (h2 : term120 m n) (h3 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157240 m n h1 h2 h3) (@lem156813 m n h2)). Qed.
Lemma lem157242 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : (term119 m n) = False.
Proof. exact (prop_ext (fun h4 : term119 m n => @lem157239 m n h1 h2 h3) (fun h4 : False => @lem156753 m n h2)). Qed.
Lemma lem157243 (m : nat) (n : nat) (h1 : term34) (h2 : term119 m n) (h3 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157242 m n h1 h2 h3) (@lem156753 m n h2)). Qed.
Lemma lem157244 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : False.
Proof. exact (or_elim (@lem156688 m n h2) (fun h0 : term119 m n => @lem157243 m n h1 h0 h2) (fun h0 : term120 m n => @lem157241 m n h1 h0 h2)). Qed.
Lemma lem157245 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : (term47 m n) = False.
Proof. exact (prop_ext (fun h3 : term47 m n => @lem157244 m n h1 h2) (fun h3 : False => @lem156687 m n h2)). Qed.
Lemma lem157246 (m : nat) (n : nat) (h1 : term34) (h2 : term47 m n) : False.
Proof. exact (EQ_MP (@lem157245 m n h1 h2) (@lem156687 m n h2)). Qed.
Lemma lem157247 (m : nat) (h1 : term34) (h2 : term58 m) : False.
Proof. exact (ex_elim (@lem156542 m h2) (fun n : nat => fun h0 : term57 m n => @lem157246 m n h1 h0)). Qed.
Lemma lem157248 (h1 : term34) (h2 : term3) : False.
Proof. exact (ex_elim (@lem156248 h2) (fun m : nat => fun h0 : term63 m => @lem157247 m h1 h0)). Qed.
Lemma lem157249 (h1 : term3) : term142.
Proof. exact (fun h0 : term34 => @lem157248 h0 h1). Qed.
Lemma lem157250 : term142 = term35.
Proof. exact (@lem69 term34). Qed.
Lemma lem157251 (h1 : term3) : term35.
Proof. exact (EQ_MP (@lem157250) (@lem157249 h1)). Qed.
Lemma lem157252 : term40.
Proof. exact (fun h0 : term3 => @lem157251 h0). Qed.
Lemma lem157253 : term4.
Proof. exact (EQ_MP (@lem156156) (@lem157252)). Qed.
Lemma lem157255 : term4.
Proof. exact (@lem155946 (@lem157253)). Qed.
Lemma lem157256 (h1 : term3) : term8.
Proof. exact (@lem157255 (@lem155931 h1)). Qed.
Lemma lem157257 (h1 : term3) : False.
Proof. exact (@lem157256 h1 (@lem155916)). Qed.
Lemma lem157258 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem157257 h1) (fun h2 : False => @lem155931 h1)). Qed.
Lemma lem157259 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem157258 h1) (@lem155931 h1)). Qed.
Lemma lem157260 : term2.
Proof. exact (fun h0 : term3 => @lem157259 h0). Qed.
Lemma lem157261 : term1.
Proof. exact (EQ_MP (@lem155930) (@lem157260)). Qed.
