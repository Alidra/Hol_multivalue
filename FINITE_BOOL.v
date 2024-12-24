Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_BOOL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_BOOL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4595894 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4595895 : (@FINITE Prop (@UNIV Prop)) = term1.
Proof. exact (@lem4595894 (@FINITE Prop (@UNIV Prop))). Qed.
Lemma lem4595896 : term1 = (@FINITE Prop (@UNIV Prop)).
Proof. exact (SYM (@lem4595895)). Qed.
Lemma lem4595897 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem4595898 : term3.
Proof. exact (@lem3863773 Prop). Qed.
Lemma lem4595902 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem4595903 : term5.
Proof. exact (fun h0 : term4 => @lem4595902 h0). Qed.
Lemma lem4595904 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem4595905 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem4595906 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem4595904 h2 (@lem4595905 h1)). Qed.
Lemma lem4595907 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem4595906 h1 h0). Qed.
Lemma lem4595908 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem4595909 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem4595907 h1 (@lem4595908 h2)). Qed.
Lemma lem4595910 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem4595909 h0 h1). Qed.
Lemma lem4595911 : term7.
Proof. exact (fun h0 : term5 => @lem4595910 h0). Qed.
Lemma lem4595914 : term5.
Proof. exact (@lem4595911 (@lem4595903)). Qed.
Lemma lem4595930 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4595931 : term8 = term9.
Proof. exact (@lem4595930 term10). Qed.
Lemma lem4595932 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem4595933 : term12 = term13.
Proof. exact (MK_COMB (@lem4595932) (@lem4595931)). Qed.
Lemma lem4595936 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem4595943 : term4 = term15.
Proof. exact (MK_COMB (@lem4595936) (@lem4595933)). Qed.
Lemma lem4595946 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem4595955 (s : Prop -> Prop) (n : nat) : ((@HAS_SIZE Prop s n) = (term16 s n)) = ((@HAS_SIZE Prop s n) = (term16 s n)).
Proof. exact (eq_refl ((@HAS_SIZE Prop s n) = (term16 s n))). Qed.
Lemma lem4595956 (s : Prop -> Prop) : (term17 s) = (term17 s).
Proof. exact (fun_ext (fun n : nat => @lem4595955 s n)). Qed.
Lemma lem4595957 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4595958 (s : Prop -> Prop) : (term18 s) = (term18 s).
Proof. exact (MK_COMB (@lem4595957) (@lem4595956 s)). Qed.
Lemma lem4595959 : term19 = term19.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4595958 s)). Qed.
Lemma lem4595960 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4595961 : term3 = term3.
Proof. exact (MK_COMB (@lem4595960) (@lem4595959)). Qed.
Lemma lem4595962 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4595963 : term11 = term11.
Proof. exact (MK_COMB (@lem4595962) (@lem4595961)). Qed.
Lemma lem4595964 : term13 = term13.
Proof. exact (MK_COMB (@lem4595963) (@lem4595946)). Qed.
Lemma lem4595969 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem4595970 : term15 = term15.
Proof. exact (MK_COMB (@lem4595969) (@lem4595964)). Qed.
Lemma lem4595991 : term4 = term15.
Proof. exact (TRANS (@lem4595943) (@lem4595970)). Qed.
Lemma lem4595992 : term15 = term4.
Proof. exact (SYM (@lem4595991)). Qed.
Lemma lem4595994 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem4596001 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem4596012 (s : Prop -> Prop) (n : nat) : (term20 s n) = (term21 s n).
Proof. exact (@lem17045 (@FINITE Prop s) ((@CARD Prop s) = n)). Qed.
Lemma lem4596018 (s : Prop -> Prop) (n : nat) : (term22 s n) = (term22 s n).
Proof. exact (eq_refl (term22 s n)). Qed.
Lemma lem4596020 (s : Prop -> Prop) (n : nat) : (term23 s n) = (term23 s n).
Proof. exact (eq_refl (term23 s n)). Qed.
Lemma lem4596021 (s : Prop -> Prop) (n : nat) : (term24 s n) = (term25 s n).
Proof. exact (MK_COMB (@lem4596020 s n) (@lem4596012 s n)). Qed.
Lemma lem4596022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4596023 (s : Prop -> Prop) (n : nat) : (term26 s n) = (term27 s n).
Proof. exact (MK_COMB (@lem4596022) (@lem4596021 s n)). Qed.
Lemma lem4596024 (s : Prop -> Prop) (n : nat) : (term28 s n) = (term29 s n).
Proof. exact (MK_COMB (@lem4596023 s n) (@lem4596018 s n)). Qed.
Lemma lem4596025 (s : Prop -> Prop) (n : nat) : ((@HAS_SIZE Prop s n) = (term16 s n)) = (term28 s n).
Proof. exact (@lem17784 (@HAS_SIZE Prop s n) (term16 s n)). Qed.
Lemma lem4596026 (s : Prop -> Prop) (n : nat) : ((@HAS_SIZE Prop s n) = (term16 s n)) = (term29 s n).
Proof. exact (TRANS (@lem4596025 s n) (@lem4596024 s n)). Qed.
Lemma lem4596027 (s : Prop -> Prop) : (term17 s) = (term30 s).
Proof. exact (fun_ext (fun n : nat => @lem4596026 s n)). Qed.
Lemma lem4596028 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4596029 (s : Prop -> Prop) : (term18 s) = (term31 s).
Proof. exact (MK_COMB (@lem4596028) (@lem4596027 s)). Qed.
Lemma lem4596030 : term19 = term32.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4596029 s)). Qed.
Lemma lem4596031 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4596032 : term3 = term33.
Proof. exact (MK_COMB (@lem4596031) (@lem4596030)). Qed.
Lemma lem4596038 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4596039 (P : nat -> Prop) (Q : nat -> Prop) : (term36 P Q) = (term37 P Q).
Proof. exact (@lem4596038 nat P Q). Qed.
Lemma lem4596040 (s : Prop -> Prop) : (term38 s) = (term39 s).
Proof. exact (@lem4596039 (term40 s) (term41 s)). Qed.
Lemma lem4596041 (s : Prop -> Prop) (n : nat) : (term42 s n) = (term25 s n).
Proof. exact (eq_refl (term42 s n)). Qed.
Lemma lem4596042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4596043 (s : Prop -> Prop) (n : nat) : (term43 s n) = (term27 s n).
Proof. exact (MK_COMB (@lem4596042) (@lem4596041 s n)). Qed.
Lemma lem4596044 (s : Prop -> Prop) (n : nat) : (term44 s n) = (term22 s n).
Proof. exact (eq_refl (term44 s n)). Qed.
Lemma lem4596045 (s : Prop -> Prop) (n : nat) : (term45 s n) = (term29 s n).
Proof. exact (MK_COMB (@lem4596043 s n) (@lem4596044 s n)). Qed.
Lemma lem4596046 (s : Prop -> Prop) : (term46 s) = (term30 s).
Proof. exact (fun_ext (fun n : nat => @lem4596045 s n)). Qed.
Lemma lem4596047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4596048 (s : Prop -> Prop) : (term38 s) = (term31 s).
Proof. exact (MK_COMB (@lem4596047) (@lem4596046 s)). Qed.
Lemma lem4596049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4596050 (s : Prop -> Prop) : (term47 s) = (term48 s).
Proof. exact (MK_COMB (@lem4596049) (@lem4596048 s)). Qed.
Lemma lem4596051 (s : Prop -> Prop) (n : nat) : (term42 s n) = (term25 s n).
Proof. exact (eq_refl (term42 s n)). Qed.
Lemma lem4596052 (s : Prop -> Prop) : (term49 s) = (term40 s).
Proof. exact (fun_ext (fun n : nat => @lem4596051 s n)). Qed.
Lemma lem4596053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4596054 (s : Prop -> Prop) : (term50 s) = (term51 s).
Proof. exact (MK_COMB (@lem4596053) (@lem4596052 s)). Qed.
Lemma lem4596055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4596056 (s : Prop -> Prop) : (term52 s) = (term53 s).
Proof. exact (MK_COMB (@lem4596055) (@lem4596054 s)). Qed.
Lemma lem4596057 (s : Prop -> Prop) (n : nat) : (term44 s n) = (term22 s n).
Proof. exact (eq_refl (term44 s n)). Qed.
Lemma lem4596058 (s : Prop -> Prop) : (term54 s) = (term41 s).
Proof. exact (fun_ext (fun n : nat => @lem4596057 s n)). Qed.
Lemma lem4596059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4596060 (s : Prop -> Prop) : (term55 s) = (term56 s).
Proof. exact (MK_COMB (@lem4596059) (@lem4596058 s)). Qed.
Lemma lem4596061 (s : Prop -> Prop) : (term39 s) = (term57 s).
Proof. exact (MK_COMB (@lem4596056 s) (@lem4596060 s)). Qed.
Lemma lem4596062 (s : Prop -> Prop) : ((term38 s) = (term39 s)) = ((term31 s) = (term57 s)).
Proof. exact (MK_COMB (@lem4596050 s) (@lem4596061 s)). Qed.
Lemma lem4596063 (s : Prop -> Prop) : (term31 s) = (term57 s).
Proof. exact (EQ_MP (@lem4596062 s) (@lem4596040 s)). Qed.
Lemma lem4596160 : term32 = term58.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4596063 s)). Qed.
Lemma lem4596161 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4596162 : term33 = term59.
Proof. exact (MK_COMB (@lem4596161) (@lem4596160)). Qed.
Lemma lem4596164 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4596165 (P : type920) (Q : type920) : (term60 P Q) = (term61 P Q).
Proof. exact (@lem4596164 (Prop -> Prop) P Q). Qed.
Lemma lem4596166 : term62 = term63.
Proof. exact (@lem4596165 term64 term65). Qed.
Lemma lem4596167 (s : Prop -> Prop) : (term66 s) = (term51 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem4596168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4596169 (s : Prop -> Prop) : (term67 s) = (term53 s).
Proof. exact (MK_COMB (@lem4596168) (@lem4596167 s)). Qed.
Lemma lem4596170 (s : Prop -> Prop) : (term68 s) = (term56 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem4596171 (s : Prop -> Prop) : (term69 s) = (term57 s).
Proof. exact (MK_COMB (@lem4596169 s) (@lem4596170 s)). Qed.
Lemma lem4596172 : term70 = term58.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4596171 s)). Qed.
Lemma lem4596173 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4596174 : term62 = term59.
Proof. exact (MK_COMB (@lem4596173) (@lem4596172)). Qed.
Lemma lem4596175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4596176 : term71 = term72.
Proof. exact (MK_COMB (@lem4596175) (@lem4596174)). Qed.
Lemma lem4596177 (s : Prop -> Prop) : (term66 s) = (term51 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem4596178 : term73 = term64.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4596177 s)). Qed.
Lemma lem4596179 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4596180 : term74 = term75.
Proof. exact (MK_COMB (@lem4596179) (@lem4596178)). Qed.
Lemma lem4596181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4596182 : term76 = term77.
Proof. exact (MK_COMB (@lem4596181) (@lem4596180)). Qed.
Lemma lem4596183 (s : Prop -> Prop) : (term68 s) = (term56 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem4596184 : term78 = term65.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4596183 s)). Qed.
Lemma lem4596185 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4596186 : term79 = term80.
Proof. exact (MK_COMB (@lem4596185) (@lem4596184)). Qed.
Lemma lem4596187 : term63 = term81.
Proof. exact (MK_COMB (@lem4596182) (@lem4596186)). Qed.
Lemma lem4596188 : (term62 = term63) = (term59 = term81).
Proof. exact (MK_COMB (@lem4596176) (@lem4596187)). Qed.
Lemma lem4596189 : term59 = term81.
Proof. exact (EQ_MP (@lem4596188) (@lem4596166)). Qed.
Lemma lem4596296 : term33 = term81.
Proof. exact (TRANS (@lem4596162) (@lem4596189)). Qed.
Lemma lem4596297 : term3 = term81.
Proof. exact (TRANS (@lem4596032) (@lem4596296)). Qed.
Lemma lem4596298 (h1 : term3) : term81.
Proof. exact (EQ_MP (@lem4596297) (@lem4595994 h1)). Qed.
Lemma lem4596304 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem4596310 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem4596333 (s : Prop -> Prop) (n : nat) : (term22 s n) = (term22 s n).
Proof. exact (eq_refl (term22 s n)). Qed.
Lemma lem4596334 (s : Prop -> Prop) : (term41 s) = (term41 s).
Proof. exact (fun_ext (fun n : nat => @lem4596333 s n)). Qed.
Lemma lem4596335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4596336 (s : Prop -> Prop) : (term56 s) = (term56 s).
Proof. exact (MK_COMB (@lem4596335) (@lem4596334 s)). Qed.
Lemma lem4596337 : term65 = term65.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4596336 s)). Qed.
Lemma lem4596338 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4596339 : term80 = term80.
Proof. exact (MK_COMB (@lem4596338) (@lem4596337)). Qed.
Lemma lem4596364 (s : Prop -> Prop) (n : nat) : (term25 s n) = (term25 s n).
Proof. exact (eq_refl (term25 s n)). Qed.
Lemma lem4596365 (s : Prop -> Prop) : (term40 s) = (term40 s).
Proof. exact (fun_ext (fun n : nat => @lem4596364 s n)). Qed.
Lemma lem4596366 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4596367 (s : Prop -> Prop) : (term51 s) = (term51 s).
Proof. exact (MK_COMB (@lem4596366) (@lem4596365 s)). Qed.
Lemma lem4596368 : term64 = term64.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4596367 s)). Qed.
Lemma lem4596369 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4596370 : term75 = term75.
Proof. exact (MK_COMB (@lem4596369) (@lem4596368)). Qed.
Lemma lem4596371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4596372 : term77 = term77.
Proof. exact (MK_COMB (@lem4596371) (@lem4596370)). Qed.
Lemma lem4596373 : term81 = term81.
Proof. exact (MK_COMB (@lem4596372) (@lem4596339)). Qed.
Lemma lem4596374 (h1 : term3) : term81.
Proof. exact (EQ_MP (@lem4596373) (@lem4596298 h1)). Qed.
Lemma lem4596386 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem4596387 (h1 : term3) : term80.
Proof. exact (proj2 (@lem4596374 h1)). Qed.
Lemma lem4596392 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem4596396 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem4596436 (s : Prop -> Prop) (n : nat) : (term22 s n) = (term82 s n).
Proof. exact (@lem19490 (@FINITE Prop s) (term83 s n) ((@CARD Prop s) = n)). Qed.
Lemma lem4596437 (s : Prop -> Prop) : (term41 s) = (term84 s).
Proof. exact (fun_ext (fun n : nat => @lem4596436 s n)). Qed.
Lemma lem4596438 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4596439 (s : Prop -> Prop) : (term56 s) = (term85 s).
Proof. exact (MK_COMB (@lem4596438) (@lem4596437 s)). Qed.
Lemma lem4596440 : term65 = term86.
Proof. exact (fun_ext (fun s : Prop -> Prop => @lem4596439 s)). Qed.
Lemma lem4596441 : (@all (Prop -> Prop)) = (@all (Prop -> Prop)).
Proof. exact (eq_refl (@all (Prop -> Prop))). Qed.
Lemma lem4596443 : term80 = term87.
Proof. exact (MK_COMB (@lem4596441) (@lem4596440)). Qed.
Lemma lem4596444 (h1 : term3) : term87.
Proof. exact (EQ_MP (@lem4596443) (@lem4596387 h1)). Qed.
Lemma lem4596451 (_55193 : Prop -> Prop) (h1 : term3) : term88 _55193.
Proof. exact (@lem4596444 h1 _55193). Qed.
Lemma lem4596452 (_55193 : Prop -> Prop) : (term88 _55193) = (term85 _55193).
Proof. exact (eq_refl (term88 _55193)). Qed.
Lemma lem4596453 (_55193 : Prop -> Prop) (h1 : term3) : term85 _55193.
Proof. exact (EQ_MP (@lem4596452 _55193) (@lem4596451 _55193 h1)). Qed.
Lemma lem4596454 (_55193 : Prop -> Prop) (_55194 : nat) (h1 : term3) : term89 _55193 _55194.
Proof. exact (@lem4596453 _55193 h1 _55194). Qed.
Lemma lem4596455 (_55193 : Prop -> Prop) (_55194 : nat) : (term89 _55193 _55194) = (term82 _55193 _55194).
Proof. exact (eq_refl (term89 _55193 _55194)). Qed.
Lemma lem4596456 (_55193 : Prop -> Prop) (_55194 : nat) (h1 : term3) : term82 _55193 _55194.
Proof. exact (EQ_MP (@lem4596455 _55193 _55194) (@lem4596454 _55193 _55194 h1)). Qed.
Lemma lem4596460 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem4596462 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem4596478 (_55194 : nat) (_55193 : Prop -> Prop) (h1 : term3) : term90 _55194 _55193.
Proof. exact (proj1 (@lem4596456 _55193 _55194 h1)). Qed.
Lemma lem4596553 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem4596554 (h1 : term10) : term91.
Proof. exact (fun h0 : term9 => @lem4596553 h1). Qed.
Lemma lem4596556 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4596557 : term91 = term10.
Proof. exact (@lem4596556 term10). Qed.
Lemma lem4596558 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem4596557) (@lem4596554 h1)). Qed.
Lemma lem4596564 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4596565 (_55193 : Prop -> Prop) (_55194 : nat) : (term90 _55194 _55193) = (term93 _55193 _55194).
Proof. exact (@lem4596564 (@FINITE Prop _55193) (term83 _55193 _55194)). Qed.
Lemma lem4596571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4596572 (_55193 : Prop -> Prop) (_55194 : nat) : (term94 _55194 _55193) = (term95 _55193 _55194).
Proof. exact (MK_COMB (@lem4596571) (@lem4596565 _55193 _55194)). Qed.
Lemma lem4596578 (_55193 : Prop -> Prop) (_55194 : nat) : (term93 _55193 _55194) = (term93 _55193 _55194).
Proof. exact (eq_refl (term93 _55193 _55194)). Qed.
Lemma lem4596579 (_55193 : Prop -> Prop) (_55194 : nat) : ((term90 _55194 _55193) = (term93 _55193 _55194)) = ((term93 _55193 _55194) = (term93 _55193 _55194)).
Proof. exact (MK_COMB (@lem4596572 _55193 _55194) (@lem4596578 _55193 _55194)). Qed.
Lemma lem4596581 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4596582 (x : Prop) : (x = x) = True.
Proof. exact (@lem4596581 Prop x). Qed.
Lemma lem4596583 (_55193 : Prop -> Prop) (_55194 : nat) : ((term93 _55193 _55194) = (term93 _55193 _55194)) = True.
Proof. exact (@lem4596582 (term93 _55193 _55194)). Qed.
Lemma lem4596584 (_55193 : Prop -> Prop) (_55194 : nat) : ((term90 _55194 _55193) = (term93 _55193 _55194)) = True.
Proof. exact (TRANS (@lem4596579 _55193 _55194) (@lem4596583 _55193 _55194)). Qed.
Lemma lem4596585 (_55193 : Prop -> Prop) (_55194 : nat) : True = ((term90 _55194 _55193) = (term93 _55193 _55194)).
Proof. exact (SYM (@lem4596584 _55193 _55194)). Qed.
Lemma lem4596586 (_55193 : Prop -> Prop) (_55194 : nat) : (term90 _55194 _55193) = (term93 _55193 _55194).
Proof. exact (EQ_MP (@lem4596585 _55193 _55194) (@lem0)). Qed.
Lemma lem4596587 (_55193 : Prop -> Prop) (_55194 : nat) (h1 : term3) : term93 _55193 _55194.
Proof. exact (EQ_MP (@lem4596586 _55193 _55194) (@lem4596478 _55194 _55193 h1)). Qed.
Lemma lem4596589 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4596590 (_55194 : nat) (_55193 : Prop -> Prop) : (term93 _55193 _55194) = (term97 _55194 _55193).
Proof. exact (@lem4596589 (term83 _55193 _55194) (@FINITE Prop _55193)). Qed.
Lemma lem4596592 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4596593 (_55193 : Prop -> Prop) (_55194 : nat) : (term99 _55193 _55194) = (@HAS_SIZE Prop _55193 _55194).
Proof. exact (@lem4596592 (@HAS_SIZE Prop _55193 _55194)). Qed.
Lemma lem4596594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4596595 (_55193 : Prop -> Prop) (_55194 : nat) : (term100 _55193 _55194) = (term101 _55193 _55194).
Proof. exact (MK_COMB (@lem4596594) (@lem4596593 _55193 _55194)). Qed.
Lemma lem4596596 (_55193 : Prop -> Prop) : (@FINITE Prop _55193) = (@FINITE Prop _55193).
Proof. exact (eq_refl (@FINITE Prop _55193)). Qed.
Lemma lem4596597 (_55194 : nat) (_55193 : Prop -> Prop) : (term97 _55194 _55193) = (term102 _55194 _55193).
Proof. exact (MK_COMB (@lem4596595 _55193 _55194) (@lem4596596 _55193)). Qed.
Lemma lem4596598 (_55194 : nat) (_55193 : Prop -> Prop) : (term93 _55193 _55194) = (term102 _55194 _55193).
Proof. exact (TRANS (@lem4596590 _55194 _55193) (@lem4596597 _55194 _55193)). Qed.
Lemma lem4596601 (_55194 : nat) (_55193 : Prop -> Prop) (h1 : term3) : term102 _55194 _55193.
Proof. exact (EQ_MP (@lem4596598 _55194 _55193) (@lem4596587 _55193 _55194 h1)). Qed.
Lemma lem4596602 (h1 : term3) : term103.
Proof. exact (@lem4596601 term104 (@UNIV Prop) h1). Qed.
Lemma lem4596605 (h1 : term3) (h2 : term10) : @FINITE Prop (@UNIV Prop).
Proof. exact (@lem4596602 h1 (@lem4596558 h2)). Qed.
Lemma lem4596606 (h1 : term3) (h2 : term10) : term105.
Proof. exact (fun h0 : term2 => @lem4596605 h1 h2). Qed.
Lemma lem4596608 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4596609 : term105 = (@FINITE Prop (@UNIV Prop)).
Proof. exact (@lem4596608 (@FINITE Prop (@UNIV Prop))). Qed.
Lemma lem4596610 (h1 : term3) (h2 : term10) : @FINITE Prop (@UNIV Prop).
Proof. exact (EQ_MP (@lem4596609) (@lem4596606 h1 h2)). Qed.
Lemma lem4596613 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4596615 : term2 = term106.
Proof. exact (@lem4596613 (@FINITE Prop (@UNIV Prop))). Qed.
Lemma lem4596618 (h1 : term2) : term106.
Proof. exact (EQ_MP (@lem4596615) (@lem4596460 h1)). Qed.
Lemma lem4596621 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (@lem4596618 h2 (@lem4596610 h1 h3)). Qed.
Lemma lem4596622 (h1 : term3) (h2 : term2) (h3 : term10) : term107.
Proof. exact (fun h0 : ~ False => @lem4596621 h1 h2 h3). Qed.
Lemma lem4596624 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4596625 : term107 = False.
Proof. exact (@lem4596624 False). Qed.
Lemma lem4596626 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596625) (@lem4596622 h1 h2 h3)). Qed.
Lemma lem4596627 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem4596626 h1 h2 h3) (fun h4 : False => @lem4596462 h3)). Qed.
Lemma lem4596628 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596627 h1 h2 h3) (@lem4596462 h3)). Qed.
Lemma lem4596629 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem4596628 h1 h2 h3) (fun h4 : False => @lem4596460 h2)). Qed.
Lemma lem4596630 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596629 h1 h2 h3) (@lem4596460 h2)). Qed.
Lemma lem4596631 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem4596630 h1 h2 h3) (fun h4 : False => @lem4596396 h3)). Qed.
Lemma lem4596632 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596631 h1 h2 h3) (@lem4596396 h3)). Qed.
Lemma lem4596633 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem4596632 h1 h2 h3) (fun h4 : False => @lem4596392 h2)). Qed.
Lemma lem4596634 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596633 h1 h2 h3) (@lem4596392 h2)). Qed.
Lemma lem4596635 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem4596634 h1 h2 h3) (fun h4 : False => @lem4596396 h3)). Qed.
Lemma lem4596636 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596635 h1 h2 h3) (@lem4596396 h3)). Qed.
Lemma lem4596637 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem4596636 h1 h2 h3) (fun h4 : False => @lem4596392 h2)). Qed.
Lemma lem4596638 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596637 h1 h2 h3) (@lem4596392 h2)). Qed.
Lemma lem4596639 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem4596638 h1 h2 h3) (fun h4 : False => @lem4596386 h3)). Qed.
Lemma lem4596640 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596639 h1 h2 h3) (@lem4596386 h3)). Qed.
Lemma lem4596641 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem4596640 h1 h2 h3) (fun h4 : False => @lem4596310 h2)). Qed.
Lemma lem4596642 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596641 h1 h2 h3) (@lem4596310 h2)). Qed.
Lemma lem4596643 (h1 : term3) (h2 : term2) (h3 : term10) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem4596642 h1 h2 h3) (fun h4 : False => @lem4596304 h3)). Qed.
Lemma lem4596644 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596643 h1 h2 h3) (@lem4596304 h3)). Qed.
Lemma lem4596645 (h1 : term3) (h2 : term2) (h3 : term10) : term2 = False.
Proof. exact (prop_ext (fun h4 : term2 => @lem4596644 h1 h2 h3) (fun h4 : False => @lem4596001 h2)). Qed.
Lemma lem4596646 (h1 : term3) (h2 : term2) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem4596645 h1 h2 h3) (@lem4596001 h2)). Qed.
Lemma lem4596647 (h1 : term3) (h2 : term2) : term8.
Proof. exact (fun h0 : term10 => @lem4596646 h1 h2 h0). Qed.
Lemma lem4596648 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem4596649 (h1 : term3) (h2 : term2) : term9.
Proof. exact (EQ_MP (@lem4596648) (@lem4596647 h1 h2)). Qed.
Lemma lem4596650 (h1 : term2) : term13.
Proof. exact (fun h0 : term3 => @lem4596649 h0 h1). Qed.
Lemma lem4596651 : term15.
Proof. exact (fun h0 : term2 => @lem4596650 h0). Qed.
Lemma lem4596652 : term4.
Proof. exact (EQ_MP (@lem4595992) (@lem4596651)). Qed.
Lemma lem4596654 : term4.
Proof. exact (@lem4595914 (@lem4596652)). Qed.
Lemma lem4596655 (h1 : term2) : term12.
Proof. exact (@lem4596654 (@lem4595897 h1)). Qed.
Lemma lem4596656 (h1 : term2) : term8.
Proof. exact (@lem4596655 h1 (@lem4595898)). Qed.
Lemma lem4596657 (h1 : term2) : False.
Proof. exact (@lem4596656 h1 (@lem4594547)). Qed.
Lemma lem4596658 (h1 : term2) : term2 = False.
Proof. exact (prop_ext (fun h2 : term2 => @lem4596657 h1) (fun h2 : False => @lem4595897 h1)). Qed.
Lemma lem4596659 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem4596658 h1) (@lem4595897 h1)). Qed.
Lemma lem4596660 : term1.
Proof. exact (fun h0 : term2 => @lem4596659 h0). Qed.
Lemma lem4596661 : @FINITE Prop (@UNIV Prop).
Proof. exact (EQ_MP (@lem4595896) (@lem4596660)). Qed.
