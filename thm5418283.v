Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5418283_term_abbrevs.
Require Import INT_POS_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367767_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm5400877_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5413138 (m : nat) (x : nat) (n : nat) : ((term0 m x n) = (term1 m x n)) = ((term0 m x n) = (term1 m x n)).
Proof. exact (eq_refl ((term0 m x n) = (term1 m x n))). Qed.
Lemma lem5413139 (m : nat) (n : nat) : (term2 m n) = (term2 m n).
Proof. exact (fun_ext (fun x : nat => @lem5413138 m x n)). Qed.
Lemma lem5413140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5413141 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem5413140) (@lem5413139 m n)). Qed.
Lemma lem5413146 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem5413148 (m : nat) (n : nat) : (term5 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem5413146 m n) (@lem5413141 m n)). Qed.
Lemma lem5413151 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (@lem16933 (term7 m n)). Qed.
Lemma lem5413160 (m : nat) (x : nat) (n : nat) : (term8 m x n) = (term9 m x n).
Proof. exact (@lem17045 (Peano.le m x) (term7 x n)). Qed.
Lemma lem5413172 (m : nat) (x : nat) (n : nat) : (term10 m x n) = (term11 m x n).
Proof. exact (@lem17045 (Peano.le m x) (Peano.le x n)). Qed.
Lemma lem5413175 (m : nat) (x : nat) (n : nat) : (term1 m x n) = (term1 m x n).
Proof. exact (eq_refl (term1 m x n)). Qed.
Lemma lem5413176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413177 (m : nat) (x : nat) (n : nat) : (term12 m x n) = (term13 m x n).
Proof. exact (MK_COMB (@lem5413176) (@lem5413160 m x n)). Qed.
Lemma lem5413178 (m : nat) (x : nat) (n : nat) : (term14 m x n) = (term15 m x n).
Proof. exact (MK_COMB (@lem5413177 m x n) (@lem5413175 m x n)). Qed.
Lemma lem5413180 (m : nat) (x : nat) (n : nat) : (term16 m x n) = (term16 m x n).
Proof. exact (eq_refl (term16 m x n)). Qed.
Lemma lem5413181 (m : nat) (x : nat) (n : nat) : (term17 m x n) = (term18 m x n).
Proof. exact (MK_COMB (@lem5413180 m x n) (@lem5413172 m x n)). Qed.
Lemma lem5413182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413183 (m : nat) (x : nat) (n : nat) : (term19 m x n) = (term20 m x n).
Proof. exact (MK_COMB (@lem5413182) (@lem5413181 m x n)). Qed.
Lemma lem5413184 (m : nat) (x : nat) (n : nat) : (term21 m x n) = (term22 m x n).
Proof. exact (MK_COMB (@lem5413183 m x n) (@lem5413178 m x n)). Qed.
Lemma lem5413185 (m : nat) (x : nat) (n : nat) : ((term0 m x n) = (term1 m x n)) = (term21 m x n).
Proof. exact (@lem17784 (term0 m x n) (term1 m x n)). Qed.
Lemma lem5413186 (m : nat) (x : nat) (n : nat) : ((term0 m x n) = (term1 m x n)) = (term22 m x n).
Proof. exact (TRANS (@lem5413185 m x n) (@lem5413184 m x n)). Qed.
Lemma lem5413187 (m : nat) (n : nat) : (term2 m n) = (term23 m n).
Proof. exact (fun_ext (fun x : nat => @lem5413186 m x n)). Qed.
Lemma lem5413188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5413189 (m : nat) (n : nat) : (term3 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem5413188) (@lem5413187 m n)). Qed.
Lemma lem5413190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413191 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem5413190) (@lem5413151 m n)). Qed.
Lemma lem5413192 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem5413191 m n) (@lem5413189 m n)). Qed.
Lemma lem5413193 (m : nat) (n : nat) : (term5 m n) = (term27 m n).
Proof. exact (@lem17265 (term29 m n) (term3 m n)). Qed.
Lemma lem5413194 (m : nat) (n : nat) : (term5 m n) = (term28 m n).
Proof. exact (TRANS (@lem5413193 m n) (@lem5413192 m n)). Qed.
Lemma lem5413195 (m : nat) (n : nat) : (term5 m n) = (term28 m n).
Proof. exact (TRANS (@lem5413148 m n) (@lem5413194 m n)). Qed.
Lemma lem5413196 (m : nat) (x : nat) (n : nat) : (term22 m x n) = (term22 m x n).
Proof. exact (eq_refl (term22 m x n)). Qed.
Lemma lem5413197 (m : nat) (n : nat) : (term23 m n) = (term23 m n).
Proof. exact (fun_ext (fun x : nat => @lem5413196 m x n)). Qed.
Lemma lem5413198 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5413199 (m : nat) (n : nat) : (term24 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem5413198) (@lem5413197 m n)). Qed.
Lemma lem5413202 (m : nat) (n : nat) : (term26 m n) = (term26 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem5413203 (m : nat) (n : nat) : (term28 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem5413202 m n) (@lem5413199 m n)). Qed.
Lemma lem5413228 (m : nat) (n : nat) : (term5 m n) = (term28 m n).
Proof. exact (TRANS (@lem5413195 m n) (@lem5413203 m n)). Qed.
Lemma lem5413230 (m : nat) : (S m) = (term30 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5413231 (n : nat) : (S n) = (term30 n).
Proof. exact (@lem5413230 n). Qed.
Lemma lem5413232 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem5413233 (m : nat) (n : nat) : (term7 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem5413232 m) (@lem5413231 n)). Qed.
Lemma lem5413234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413235 (m : nat) (n : nat) : (term26 m n) = (term32 m n).
Proof. exact (MK_COMB (@lem5413234) (@lem5413233 m n)). Qed.
Lemma lem5413237 (m : nat) : (S m) = (term30 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5413238 (n : nat) : (S n) = (term30 n).
Proof. exact (@lem5413237 n). Qed.
Lemma lem5413239 (x : nat) : (Peano.le x) = (Peano.le x).
Proof. exact (eq_refl (Peano.le x)). Qed.
Lemma lem5413240 (x : nat) (n : nat) : (term7 x n) = (term31 x n).
Proof. exact (MK_COMB (@lem5413239 x) (@lem5413238 n)). Qed.
Lemma lem5413241 (m : nat) (x : nat) : (term33 m x) = (term33 m x).
Proof. exact (eq_refl (term33 m x)). Qed.
Lemma lem5413242 (m : nat) (x : nat) (n : nat) : (term0 m x n) = (term34 m x n).
Proof. exact (MK_COMB (@lem5413241 m x) (@lem5413240 x n)). Qed.
Lemma lem5413243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413244 (m : nat) (x : nat) (n : nat) : (term16 m x n) = (term35 m x n).
Proof. exact (MK_COMB (@lem5413243) (@lem5413242 m x n)). Qed.
Lemma lem5413245 (m : nat) (x : nat) (n : nat) : (term11 m x n) = (term11 m x n).
Proof. exact (eq_refl (term11 m x n)). Qed.
Lemma lem5413246 (m : nat) (x : nat) (n : nat) : (term18 m x n) = (term36 m x n).
Proof. exact (MK_COMB (@lem5413244 m x n) (@lem5413245 m x n)). Qed.
Lemma lem5413247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413248 (m : nat) (x : nat) (n : nat) : (term20 m x n) = (term37 m x n).
Proof. exact (MK_COMB (@lem5413247) (@lem5413246 m x n)). Qed.
Lemma lem5413250 (m : nat) : (S m) = (term30 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem5413251 (n : nat) : (S n) = (term30 n).
Proof. exact (@lem5413250 n). Qed.
Lemma lem5413252 (x : nat) : (Peano.le x) = (Peano.le x).
Proof. exact (eq_refl (Peano.le x)). Qed.
Lemma lem5413253 (x : nat) (n : nat) : (term7 x n) = (term31 x n).
Proof. exact (MK_COMB (@lem5413252 x) (@lem5413251 n)). Qed.
Lemma lem5413254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5413255 (x : nat) (n : nat) : (term29 x n) = (term38 x n).
Proof. exact (MK_COMB (@lem5413254) (@lem5413253 x n)). Qed.
Lemma lem5413256 (m : nat) (x : nat) : (term39 m x) = (term39 m x).
Proof. exact (eq_refl (term39 m x)). Qed.
Lemma lem5413257 (m : nat) (x : nat) (n : nat) : (term9 m x n) = (term40 m x n).
Proof. exact (MK_COMB (@lem5413256 m x) (@lem5413255 x n)). Qed.
Lemma lem5413258 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413259 (m : nat) (x : nat) (n : nat) : (term13 m x n) = (term41 m x n).
Proof. exact (MK_COMB (@lem5413258) (@lem5413257 m x n)). Qed.
Lemma lem5413260 (m : nat) (x : nat) (n : nat) : (term1 m x n) = (term1 m x n).
Proof. exact (eq_refl (term1 m x n)). Qed.
Lemma lem5413261 (m : nat) (x : nat) (n : nat) : (term15 m x n) = (term42 m x n).
Proof. exact (MK_COMB (@lem5413259 m x n) (@lem5413260 m x n)). Qed.
Lemma lem5413262 (m : nat) (x : nat) (n : nat) : (term22 m x n) = (term43 m x n).
Proof. exact (MK_COMB (@lem5413248 m x n) (@lem5413261 m x n)). Qed.
Lemma lem5413263 (m : nat) (n : nat) : (term23 m n) = (term44 m n).
Proof. exact (fun_ext (fun x : nat => @lem5413262 m x n)). Qed.
Lemma lem5413264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5413265 (m : nat) (n : nat) : (term24 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem5413264) (@lem5413263 m n)). Qed.
Lemma lem5413266 (m : nat) (n : nat) : (term28 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem5413235 m n) (@lem5413265 m n)). Qed.
Lemma lem5413267 (m : nat) (n : nat) : (term5 m n) = (term46 m n).
Proof. exact (TRANS (@lem5413228 m n) (@lem5413266 m n)). Qed.
Lemma lem5413348 (m : nat) (x : nat) (n : nat) : (term43 m x n) = (term43 m x n).
Proof. exact (eq_refl (term43 m x n)). Qed.
Lemma lem5413349 (m : nat) (n : nat) : (term44 m n) = (term44 m n).
Proof. exact (fun_ext (fun x : nat => @lem5413348 m x n)). Qed.
Lemma lem5413350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5413351 (m : nat) (n : nat) : (term45 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem5413350) (@lem5413349 m n)). Qed.
Lemma lem5413364 (m : nat) (n : nat) : (term32 m n) = (term32 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem5413365 (m : nat) (n : nat) : (term46 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem5413364 m n) (@lem5413351 m n)). Qed.
Lemma lem5413366 (m : nat) (n : nat) : (term5 m n) = (term46 m n).
Proof. exact (TRANS (@lem5413267 m n) (@lem5413365 m n)). Qed.
Lemma lem5413368 {A : Type'} (P : Prop) (Q : A -> Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5413369 (P : Prop) (Q : nat -> Prop) : (term49 P Q) = (term50 P Q).
Proof. exact (@lem5413368 nat P Q). Qed.
Lemma lem5413370 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (@lem5413369 (term31 m n) (term44 m n)). Qed.
Lemma lem5413371 (m : nat) (x : nat) (n : nat) : (term53 m n x) = (term43 m x n).
Proof. exact (eq_refl (term53 m n x)). Qed.
Lemma lem5413372 (m : nat) (n : nat) : (term54 m n) = (term44 m n).
Proof. exact (fun_ext (fun x : nat => @lem5413371 m x n)). Qed.
Lemma lem5413373 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5413374 (m : nat) (n : nat) : (term55 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem5413373) (@lem5413372 m n)). Qed.
Lemma lem5413375 (m : nat) (n : nat) : (term32 m n) = (term32 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem5413376 (m : nat) (n : nat) : (term51 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem5413375 m n) (@lem5413374 m n)). Qed.
Lemma lem5413377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5413378 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (MK_COMB (@lem5413377) (@lem5413376 m n)). Qed.
Lemma lem5413379 (m : nat) (x : nat) (n : nat) : (term53 m n x) = (term43 m x n).
Proof. exact (eq_refl (term53 m n x)). Qed.
Lemma lem5413380 (m : nat) (n : nat) : (term32 m n) = (term32 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem5413381 (m : nat) (x : nat) (n : nat) : (term58 m n x) = (term59 m x n).
Proof. exact (MK_COMB (@lem5413380 m n) (@lem5413379 m x n)). Qed.
Lemma lem5413382 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (fun_ext (fun x : nat => @lem5413381 m x n)). Qed.
Lemma lem5413383 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5413384 (m : nat) (n : nat) : (term52 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem5413383) (@lem5413382 m n)). Qed.
Lemma lem5413385 (m : nat) (n : nat) : ((term51 m n) = (term52 m n)) = ((term46 m n) = (term62 m n)).
Proof. exact (MK_COMB (@lem5413378 m n) (@lem5413384 m n)). Qed.
Lemma lem5413386 (m : nat) (n : nat) : (term46 m n) = (term62 m n).
Proof. exact (EQ_MP (@lem5413385 m n) (@lem5413370 m n)). Qed.
Lemma lem5413387 (m : nat) (n : nat) : (term5 m n) = (term62 m n).
Proof. exact (TRANS (@lem5413366 m n) (@lem5413386 m n)). Qed.
Lemma lem5413389 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413390 (m : nat) (n : nat) : (term31 m n) = (term64 m n).
Proof. exact (@lem5413389 m (term30 n)). Qed.
Lemma lem5413392 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5413393 (n : nat) : (term67 n) = (term68 n).
Proof. exact (@lem5413392 n term69). Qed.
Lemma lem5413394 (m : nat) : (term70 m) = (term70 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem5413395 (m : nat) (n : nat) : (term64 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem5413394 m) (@lem5413393 n)). Qed.
Lemma lem5413396 (m : nat) (n : nat) : (term31 m n) = (term71 m n).
Proof. exact (TRANS (@lem5413390 m n) (@lem5413395 m n)). Qed.
Lemma lem5413397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413398 (m : nat) (n : nat) : (term32 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem5413397) (@lem5413396 m n)). Qed.
Lemma lem5413400 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413401 (m : nat) (x : nat) : (Peano.le m x) = (term63 m x).
Proof. exact (@lem5413400 m x). Qed.
Lemma lem5413402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413403 (m : nat) (x : nat) : (term33 m x) = (term73 m x).
Proof. exact (MK_COMB (@lem5413402) (@lem5413401 m x)). Qed.
Lemma lem5413405 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413406 (x : nat) (n : nat) : (term31 x n) = (term64 x n).
Proof. exact (@lem5413405 x (term30 n)). Qed.
Lemma lem5413408 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5413409 (n : nat) : (term67 n) = (term68 n).
Proof. exact (@lem5413408 n term69). Qed.
Lemma lem5413410 (x : nat) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem5413411 (x : nat) (n : nat) : (term64 x n) = (term71 x n).
Proof. exact (MK_COMB (@lem5413410 x) (@lem5413409 n)). Qed.
Lemma lem5413412 (x : nat) (n : nat) : (term31 x n) = (term71 x n).
Proof. exact (TRANS (@lem5413406 x n) (@lem5413411 x n)). Qed.
Lemma lem5413413 (m : nat) (x : nat) (n : nat) : (term34 m x n) = (term74 m x n).
Proof. exact (MK_COMB (@lem5413403 m x) (@lem5413412 x n)). Qed.
Lemma lem5413414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413415 (m : nat) (x : nat) (n : nat) : (term35 m x n) = (term75 m x n).
Proof. exact (MK_COMB (@lem5413414) (@lem5413413 m x n)). Qed.
Lemma lem5413417 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413418 (m : nat) (x : nat) : (Peano.le m x) = (term63 m x).
Proof. exact (@lem5413417 m x). Qed.
Lemma lem5413419 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5413420 (m : nat) (x : nat) : (term76 m x) = (term77 m x).
Proof. exact (MK_COMB (@lem5413419) (@lem5413418 m x)). Qed.
Lemma lem5413421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413422 (m : nat) (x : nat) : (term39 m x) = (term78 m x).
Proof. exact (MK_COMB (@lem5413421) (@lem5413420 m x)). Qed.
Lemma lem5413424 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413425 (x : nat) (n : nat) : (Peano.le x n) = (term63 x n).
Proof. exact (@lem5413424 x n). Qed.
Lemma lem5413426 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5413427 (x : nat) (n : nat) : (term76 x n) = (term77 x n).
Proof. exact (MK_COMB (@lem5413426) (@lem5413425 x n)). Qed.
Lemma lem5413428 (m : nat) (x : nat) (n : nat) : (term11 m x n) = (term79 m x n).
Proof. exact (MK_COMB (@lem5413422 m x) (@lem5413427 x n)). Qed.
Lemma lem5413429 (m : nat) (x : nat) (n : nat) : (term36 m x n) = (term80 m x n).
Proof. exact (MK_COMB (@lem5413415 m x n) (@lem5413428 m x n)). Qed.
Lemma lem5413430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413431 (m : nat) (x : nat) (n : nat) : (term37 m x n) = (term81 m x n).
Proof. exact (MK_COMB (@lem5413430) (@lem5413429 m x n)). Qed.
Lemma lem5413433 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413434 (m : nat) (x : nat) : (Peano.le m x) = (term63 m x).
Proof. exact (@lem5413433 m x). Qed.
Lemma lem5413435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5413436 (m : nat) (x : nat) : (term76 m x) = (term77 m x).
Proof. exact (MK_COMB (@lem5413435) (@lem5413434 m x)). Qed.
Lemma lem5413437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413438 (m : nat) (x : nat) : (term39 m x) = (term78 m x).
Proof. exact (MK_COMB (@lem5413437) (@lem5413436 m x)). Qed.
Lemma lem5413440 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413441 (x : nat) (n : nat) : (term31 x n) = (term64 x n).
Proof. exact (@lem5413440 x (term30 n)). Qed.
Lemma lem5413443 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5413444 (n : nat) : (term67 n) = (term68 n).
Proof. exact (@lem5413443 n term69). Qed.
Lemma lem5413445 (x : nat) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem5413446 (x : nat) (n : nat) : (term64 x n) = (term71 x n).
Proof. exact (MK_COMB (@lem5413445 x) (@lem5413444 n)). Qed.
Lemma lem5413447 (x : nat) (n : nat) : (term31 x n) = (term71 x n).
Proof. exact (TRANS (@lem5413441 x n) (@lem5413446 x n)). Qed.
Lemma lem5413448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5413449 (x : nat) (n : nat) : (term38 x n) = (term82 x n).
Proof. exact (MK_COMB (@lem5413448) (@lem5413447 x n)). Qed.
Lemma lem5413450 (m : nat) (x : nat) (n : nat) : (term40 m x n) = (term83 m x n).
Proof. exact (MK_COMB (@lem5413438 m x) (@lem5413449 x n)). Qed.
Lemma lem5413451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413452 (m : nat) (x : nat) (n : nat) : (term41 m x n) = (term84 m x n).
Proof. exact (MK_COMB (@lem5413451) (@lem5413450 m x n)). Qed.
Lemma lem5413454 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413455 (m : nat) (x : nat) : (Peano.le m x) = (term63 m x).
Proof. exact (@lem5413454 m x). Qed.
Lemma lem5413456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413457 (m : nat) (x : nat) : (term33 m x) = (term73 m x).
Proof. exact (MK_COMB (@lem5413456) (@lem5413455 m x)). Qed.
Lemma lem5413459 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5413460 (x : nat) (n : nat) : (Peano.le x n) = (term63 x n).
Proof. exact (@lem5413459 x n). Qed.
Lemma lem5413461 (m : nat) (x : nat) (n : nat) : (term1 m x n) = (term85 m x n).
Proof. exact (MK_COMB (@lem5413457 m x) (@lem5413460 x n)). Qed.
Lemma lem5413462 (m : nat) (x : nat) (n : nat) : (term42 m x n) = (term86 m x n).
Proof. exact (MK_COMB (@lem5413452 m x n) (@lem5413461 m x n)). Qed.
Lemma lem5413463 (m : nat) (x : nat) (n : nat) : (term43 m x n) = (term87 m x n).
Proof. exact (MK_COMB (@lem5413431 m x n) (@lem5413462 m x n)). Qed.
Lemma lem5413464 (m : nat) (x : nat) (n : nat) : (term59 m x n) = (term88 m x n).
Proof. exact (MK_COMB (@lem5413398 m n) (@lem5413463 m x n)). Qed.
Lemma lem5413465 (m : nat) (n : nat) : (term61 m n) = (term89 m n).
Proof. exact (fun_ext (fun x : nat => @lem5413464 m x n)). Qed.
Lemma lem5413466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5413467 (m : nat) (n : nat) : (term62 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem5413466) (@lem5413465 m n)). Qed.
Lemma lem5413468 (m : nat) (n : nat) : (term5 m n) = (term90 m n).
Proof. exact (TRANS (@lem5413387 m n) (@lem5413467 m n)). Qed.
Lemma lem5413469 (m : nat) : term91 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5413470 (m : nat) : (term91 m) = (term92 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem5413471 (m : nat) : term92 m.
Proof. exact (EQ_MP (@lem5413470 m) (@lem5413469 m)). Qed.
Lemma lem5413472 (n : nat) : term91 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5413473 (n : nat) : (term91 n) = (term92 n).
Proof. exact (eq_refl (term91 n)). Qed.
Lemma lem5413474 (n : nat) : term92 n.
Proof. exact (EQ_MP (@lem5413473 n) (@lem5413472 n)). Qed.
Lemma lem5413475 (x : nat) : term91 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5413476 (x : nat) : (term91 x) = (term92 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem5413477 (x : nat) : term92 x.
Proof. exact (EQ_MP (@lem5413476 x) (@lem5413475 x)). Qed.
Lemma lem5413478 (_69909 : int) (_69911 : int) (_69910 : int) : (term93 _69909 _69911 _69910) = (term94 _69909 _69911 _69910).
Proof. exact (@lem2318604 (term94 _69909 _69911 _69910)). Qed.
Lemma lem5413516 (_69909 : int) (_69911 : int) (_69910 : int) : (term95 _69909 _69911 _69910) = (term96 _69909 _69911 _69910).
Proof. exact (@lem17045 (int_le _69909 _69911) (term97 _69911 _69910)). Qed.
Lemma lem5413519 (_69909 : int) (_69911 : int) : (term98 _69909 _69911) = (int_le _69909 _69911).
Proof. exact (@lem16933 (int_le _69909 _69911)). Qed.
Lemma lem5413522 (_69911 : int) (_69910 : int) : (term98 _69911 _69910) = (int_le _69911 _69910).
Proof. exact (@lem16933 (int_le _69911 _69910)). Qed.
Lemma lem5413523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413524 (_69909 : int) (_69911 : int) : (term99 _69909 _69911) = (term100 _69909 _69911).
Proof. exact (MK_COMB (@lem5413523) (@lem5413519 _69909 _69911)). Qed.
Lemma lem5413525 (_69909 : int) (_69911 : int) (_69910 : int) : (term101 _69909 _69911 _69910) = (term102 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413524 _69909 _69911) (@lem5413522 _69911 _69910)). Qed.
Lemma lem5413526 (_69909 : int) (_69911 : int) (_69910 : int) : (term103 _69909 _69911 _69910) = (term101 _69909 _69911 _69910).
Proof. exact (@lem17160 (term104 _69909 _69911) (term104 _69911 _69910)). Qed.
Lemma lem5413527 (_69909 : int) (_69911 : int) (_69910 : int) : (term103 _69909 _69911 _69910) = (term102 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413526 _69909 _69911 _69910) (@lem5413525 _69909 _69911 _69910)). Qed.
Lemma lem5413528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413529 (_69909 : int) (_69911 : int) (_69910 : int) : (term105 _69909 _69911 _69910) = (term106 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413528) (@lem5413516 _69909 _69911 _69910)). Qed.
Lemma lem5413530 (_69909 : int) (_69911 : int) (_69910 : int) : (term107 _69909 _69911 _69910) = (term108 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413529 _69909 _69911 _69910) (@lem5413527 _69909 _69911 _69910)). Qed.
Lemma lem5413531 (_69909 : int) (_69911 : int) (_69910 : int) : (term109 _69909 _69911 _69910) = (term107 _69909 _69911 _69910).
Proof. exact (@lem17160 (term110 _69909 _69911 _69910) (term111 _69909 _69911 _69910)). Qed.
Lemma lem5413532 (_69909 : int) (_69911 : int) (_69910 : int) : (term109 _69909 _69911 _69910) = (term108 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413531 _69909 _69911 _69910) (@lem5413530 _69909 _69911 _69910)). Qed.
Lemma lem5413535 (_69909 : int) (_69911 : int) : (term98 _69909 _69911) = (int_le _69909 _69911).
Proof. exact (@lem16933 (int_le _69909 _69911)). Qed.
Lemma lem5413538 (_69911 : int) (_69910 : int) : (term112 _69911 _69910) = (term97 _69911 _69910).
Proof. exact (@lem16933 (term97 _69911 _69910)). Qed.
Lemma lem5413539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413540 (_69909 : int) (_69911 : int) : (term99 _69909 _69911) = (term100 _69909 _69911).
Proof. exact (MK_COMB (@lem5413539) (@lem5413535 _69909 _69911)). Qed.
Lemma lem5413541 (_69909 : int) (_69911 : int) (_69910 : int) : (term113 _69909 _69911 _69910) = (term110 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413540 _69909 _69911) (@lem5413538 _69911 _69910)). Qed.
Lemma lem5413542 (_69909 : int) (_69911 : int) (_69910 : int) : (term114 _69909 _69911 _69910) = (term113 _69909 _69911 _69910).
Proof. exact (@lem17160 (term104 _69909 _69911) (term115 _69911 _69910)). Qed.
Lemma lem5413543 (_69909 : int) (_69911 : int) (_69910 : int) : (term114 _69909 _69911 _69910) = (term110 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413542 _69909 _69911 _69910) (@lem5413541 _69909 _69911 _69910)). Qed.
Lemma lem5413550 (_69909 : int) (_69911 : int) (_69910 : int) : (term116 _69909 _69911 _69910) = (term111 _69909 _69911 _69910).
Proof. exact (@lem17045 (int_le _69909 _69911) (int_le _69911 _69910)). Qed.
Lemma lem5413551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413552 (_69909 : int) (_69911 : int) (_69910 : int) : (term117 _69909 _69911 _69910) = (term118 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413551) (@lem5413543 _69909 _69911 _69910)). Qed.
Lemma lem5413553 (_69909 : int) (_69911 : int) (_69910 : int) : (term119 _69909 _69911 _69910) = (term120 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413552 _69909 _69911 _69910) (@lem5413550 _69909 _69911 _69910)). Qed.
Lemma lem5413554 (_69909 : int) (_69911 : int) (_69910 : int) : (term121 _69909 _69911 _69910) = (term119 _69909 _69911 _69910).
Proof. exact (@lem17160 (term96 _69909 _69911 _69910) (term102 _69909 _69911 _69910)). Qed.
Lemma lem5413555 (_69909 : int) (_69911 : int) (_69910 : int) : (term121 _69909 _69911 _69910) = (term120 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413554 _69909 _69911 _69910) (@lem5413553 _69909 _69911 _69910)). Qed.
Lemma lem5413556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413557 (_69909 : int) (_69911 : int) (_69910 : int) : (term122 _69909 _69911 _69910) = (term123 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413556) (@lem5413532 _69909 _69911 _69910)). Qed.
Lemma lem5413558 (_69909 : int) (_69911 : int) (_69910 : int) : (term124 _69909 _69911 _69910) = (term125 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413557 _69909 _69911 _69910) (@lem5413555 _69909 _69911 _69910)). Qed.
Lemma lem5413559 (_69909 : int) (_69911 : int) (_69910 : int) : (term126 _69909 _69911 _69910) = (term124 _69909 _69911 _69910).
Proof. exact (@lem17045 (term127 _69909 _69911 _69910) (term128 _69909 _69911 _69910)). Qed.
Lemma lem5413560 (_69909 : int) (_69911 : int) (_69910 : int) : (term126 _69909 _69911 _69910) = (term125 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413559 _69909 _69911 _69910) (@lem5413558 _69909 _69911 _69910)). Qed.
Lemma lem5413562 (_69909 : int) (_69910 : int) : (term129 _69909 _69910) = (term129 _69909 _69910).
Proof. exact (eq_refl (term129 _69909 _69910)). Qed.
Lemma lem5413563 (_69909 : int) (_69911 : int) (_69910 : int) : (term130 _69909 _69911 _69910) = (term131 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413562 _69909 _69910) (@lem5413560 _69909 _69911 _69910)). Qed.
Lemma lem5413564 (_69909 : int) (_69911 : int) (_69910 : int) : (term132 _69909 _69911 _69910) = (term130 _69909 _69911 _69910).
Proof. exact (@lem17160 (term97 _69909 _69910) (term133 _69909 _69911 _69910)). Qed.
Lemma lem5413565 (_69909 : int) (_69911 : int) (_69910 : int) : (term132 _69909 _69911 _69910) = (term131 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413564 _69909 _69911 _69910) (@lem5413563 _69909 _69911 _69910)). Qed.
Lemma lem5413567 (_69911 : int) : (term134 _69911) = (term134 _69911).
Proof. exact (eq_refl (term134 _69911)). Qed.
Lemma lem5413568 (_69909 : int) (_69911 : int) (_69910 : int) : (term135 _69909 _69911 _69910) = (term136 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413567 _69911) (@lem5413565 _69909 _69911 _69910)). Qed.
Lemma lem5413569 (_69909 : int) (_69911 : int) (_69910 : int) : (term137 _69909 _69911 _69910) = (term135 _69909 _69911 _69910).
Proof. exact (@lem17362 (term138 _69911) (term139 _69909 _69911 _69910)). Qed.
Lemma lem5413570 (_69909 : int) (_69911 : int) (_69910 : int) : (term137 _69909 _69911 _69910) = (term136 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413569 _69909 _69911 _69910) (@lem5413568 _69909 _69911 _69910)). Qed.
Lemma lem5413572 (_69910 : int) : (term134 _69910) = (term134 _69910).
Proof. exact (eq_refl (term134 _69910)). Qed.
Lemma lem5413573 (_69909 : int) (_69911 : int) (_69910 : int) : (term140 _69909 _69911 _69910) = (term141 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413572 _69910) (@lem5413570 _69909 _69911 _69910)). Qed.
Lemma lem5413574 (_69909 : int) (_69911 : int) (_69910 : int) : (term142 _69909 _69911 _69910) = (term140 _69909 _69911 _69910).
Proof. exact (@lem17362 (term138 _69910) (term143 _69909 _69911 _69910)). Qed.
Lemma lem5413575 (_69909 : int) (_69911 : int) (_69910 : int) : (term142 _69909 _69911 _69910) = (term141 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413574 _69909 _69911 _69910) (@lem5413573 _69909 _69911 _69910)). Qed.
Lemma lem5413577 (_69909 : int) : (term134 _69909) = (term134 _69909).
Proof. exact (eq_refl (term134 _69909)). Qed.
Lemma lem5413578 (_69909 : int) (_69911 : int) (_69910 : int) : (term144 _69909 _69911 _69910) = (term145 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413577 _69909) (@lem5413575 _69909 _69911 _69910)). Qed.
Lemma lem5413579 (_69909 : int) (_69911 : int) (_69910 : int) : (term146 _69909 _69911 _69910) = (term144 _69909 _69911 _69910).
Proof. exact (@lem17362 (term138 _69909) (term147 _69909 _69911 _69910)). Qed.
Lemma lem5413637 (_69909 : int) (_69911 : int) (_69910 : int) : (term146 _69909 _69911 _69910) = (term145 _69909 _69911 _69910).
Proof. exact (TRANS (@lem5413579 _69909 _69911 _69910) (@lem5413578 _69909 _69911 _69910)). Qed.
Lemma lem5413640 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413641 (_69909 : int) : (term138 _69909) = (term149 _69909).
Proof. exact (@lem5413640 term150 _69909). Qed.
Lemma lem5413643 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413644 : term152 = term153.
Proof. exact (@lem5413643 (NUMERAL 0)). Qed.
Lemma lem5413645 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413646 : term154 = term155.
Proof. exact (MK_COMB (@lem5413645) (@lem5413644)). Qed.
Lemma lem5413647 (_69909 : int) : (real_of_int _69909) = (real_of_int _69909).
Proof. exact (eq_refl (real_of_int _69909)). Qed.
Lemma lem5413648 (_69909 : int) : (term149 _69909) = (term156 _69909).
Proof. exact (MK_COMB (@lem5413646) (@lem5413647 _69909)). Qed.
Lemma lem5413650 (_69909 : int) : (term138 _69909) = (term156 _69909).
Proof. exact (TRANS (@lem5413641 _69909) (@lem5413648 _69909)). Qed.
Lemma lem5413653 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413654 (_69910 : int) : (term138 _69910) = (term149 _69910).
Proof. exact (@lem5413653 term150 _69910). Qed.
Lemma lem5413656 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413657 : term152 = term153.
Proof. exact (@lem5413656 (NUMERAL 0)). Qed.
Lemma lem5413658 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413659 : term154 = term155.
Proof. exact (MK_COMB (@lem5413658) (@lem5413657)). Qed.
Lemma lem5413660 (_69910 : int) : (real_of_int _69910) = (real_of_int _69910).
Proof. exact (eq_refl (real_of_int _69910)). Qed.
Lemma lem5413661 (_69910 : int) : (term149 _69910) = (term156 _69910).
Proof. exact (MK_COMB (@lem5413659) (@lem5413660 _69910)). Qed.
Lemma lem5413663 (_69910 : int) : (term138 _69910) = (term156 _69910).
Proof. exact (TRANS (@lem5413654 _69910) (@lem5413661 _69910)). Qed.
Lemma lem5413666 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413667 (_69911 : int) : (term138 _69911) = (term149 _69911).
Proof. exact (@lem5413666 term150 _69911). Qed.
Lemma lem5413669 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413670 : term152 = term153.
Proof. exact (@lem5413669 (NUMERAL 0)). Qed.
Lemma lem5413671 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413672 : term154 = term155.
Proof. exact (MK_COMB (@lem5413671) (@lem5413670)). Qed.
Lemma lem5413673 (_69911 : int) : (real_of_int _69911) = (real_of_int _69911).
Proof. exact (eq_refl (real_of_int _69911)). Qed.
Lemma lem5413674 (_69911 : int) : (term149 _69911) = (term156 _69911).
Proof. exact (MK_COMB (@lem5413672) (@lem5413673 _69911)). Qed.
Lemma lem5413676 (_69911 : int) : (term138 _69911) = (term156 _69911).
Proof. exact (TRANS (@lem5413667 _69911) (@lem5413674 _69911)). Qed.
Lemma lem5413678 (y : int) (x : int) : (term104 x y) = (term157 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5413679 (_69910 : int) (_69909 : int) : (term115 _69909 _69910) = (term158 _69910 _69909).
Proof. exact (@lem5413678 (term159 _69910) _69909). Qed.
Lemma lem5413681 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413682 (_69910 : int) (_69909 : int) : (term158 _69910 _69909) = (term160 _69910 _69909).
Proof. exact (@lem5413681 (term161 _69910) _69909). Qed.
Lemma lem5413684 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5413685 (_69910 : int) : (term164 _69910) = (term165 _69910).
Proof. exact (@lem5413684 (term159 _69910) term166). Qed.
Lemma lem5413687 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5413688 (_69910 : int) : (term167 _69910) = (term168 _69910).
Proof. exact (@lem5413687 _69910 term166). Qed.
Lemma lem5413690 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413691 : term169 = term170.
Proof. exact (@lem5413690 term69). Qed.
Lemma lem5413692 (_69910 : int) : (term171 _69910) = (term171 _69910).
Proof. exact (eq_refl (term171 _69910)). Qed.
Lemma lem5413693 (_69910 : int) : (term168 _69910) = (term172 _69910).
Proof. exact (MK_COMB (@lem5413692 _69910) (@lem5413691)). Qed.
Lemma lem5413694 (_69910 : int) : (term167 _69910) = (term172 _69910).
Proof. exact (TRANS (@lem5413688 _69910) (@lem5413693 _69910)). Qed.
Lemma lem5413695 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5413696 (_69910 : int) : (term173 _69910) = (term174 _69910).
Proof. exact (MK_COMB (@lem5413695) (@lem5413694 _69910)). Qed.
Lemma lem5413698 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413699 : term169 = term170.
Proof. exact (@lem5413698 term69). Qed.
Lemma lem5413700 (_69910 : int) : (term165 _69910) = (term175 _69910).
Proof. exact (MK_COMB (@lem5413696 _69910) (@lem5413699)). Qed.
Lemma lem5413701 (_69910 : int) : (term164 _69910) = (term175 _69910).
Proof. exact (TRANS (@lem5413685 _69910) (@lem5413700 _69910)). Qed.
Lemma lem5413702 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413703 (_69910 : int) : (term176 _69910) = (term177 _69910).
Proof. exact (MK_COMB (@lem5413702) (@lem5413701 _69910)). Qed.
Lemma lem5413704 (_69909 : int) : (real_of_int _69909) = (real_of_int _69909).
Proof. exact (eq_refl (real_of_int _69909)). Qed.
Lemma lem5413705 (_69910 : int) (_69909 : int) : (term160 _69910 _69909) = (term178 _69910 _69909).
Proof. exact (MK_COMB (@lem5413703 _69910) (@lem5413704 _69909)). Qed.
Lemma lem5413706 (_69910 : int) (_69909 : int) : (term158 _69910 _69909) = (term178 _69910 _69909).
Proof. exact (TRANS (@lem5413682 _69910 _69909) (@lem5413705 _69910 _69909)). Qed.
Lemma lem5413707 (_69910 : int) (_69909 : int) : (term115 _69909 _69910) = (term178 _69910 _69909).
Proof. exact (TRANS (@lem5413679 _69910 _69909) (@lem5413706 _69910 _69909)). Qed.
Lemma lem5413709 (y : int) (x : int) : (term104 x y) = (term157 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5413710 (_69911 : int) (_69909 : int) : (term104 _69909 _69911) = (term157 _69911 _69909).
Proof. exact (@lem5413709 _69911 _69909). Qed.
Lemma lem5413712 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413713 (_69911 : int) (_69909 : int) : (term157 _69911 _69909) = (term179 _69911 _69909).
Proof. exact (@lem5413712 (term159 _69911) _69909). Qed.
Lemma lem5413715 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5413716 (_69911 : int) : (term167 _69911) = (term168 _69911).
Proof. exact (@lem5413715 _69911 term166). Qed.
Lemma lem5413718 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413719 : term169 = term170.
Proof. exact (@lem5413718 term69). Qed.
Lemma lem5413720 (_69911 : int) : (term171 _69911) = (term171 _69911).
Proof. exact (eq_refl (term171 _69911)). Qed.
Lemma lem5413721 (_69911 : int) : (term168 _69911) = (term172 _69911).
Proof. exact (MK_COMB (@lem5413720 _69911) (@lem5413719)). Qed.
Lemma lem5413722 (_69911 : int) : (term167 _69911) = (term172 _69911).
Proof. exact (TRANS (@lem5413716 _69911) (@lem5413721 _69911)). Qed.
Lemma lem5413723 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413724 (_69911 : int) : (term180 _69911) = (term181 _69911).
Proof. exact (MK_COMB (@lem5413723) (@lem5413722 _69911)). Qed.
Lemma lem5413725 (_69909 : int) : (real_of_int _69909) = (real_of_int _69909).
Proof. exact (eq_refl (real_of_int _69909)). Qed.
Lemma lem5413726 (_69911 : int) (_69909 : int) : (term179 _69911 _69909) = (term182 _69911 _69909).
Proof. exact (MK_COMB (@lem5413724 _69911) (@lem5413725 _69909)). Qed.
Lemma lem5413727 (_69911 : int) (_69909 : int) : (term157 _69911 _69909) = (term182 _69911 _69909).
Proof. exact (TRANS (@lem5413713 _69911 _69909) (@lem5413726 _69911 _69909)). Qed.
Lemma lem5413728 (_69911 : int) (_69909 : int) : (term104 _69909 _69911) = (term182 _69911 _69909).
Proof. exact (TRANS (@lem5413710 _69911 _69909) (@lem5413727 _69911 _69909)). Qed.
Lemma lem5413730 (y : int) (x : int) : (term104 x y) = (term157 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5413731 (_69910 : int) (_69911 : int) : (term115 _69911 _69910) = (term158 _69910 _69911).
Proof. exact (@lem5413730 (term159 _69910) _69911). Qed.
Lemma lem5413733 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413734 (_69910 : int) (_69911 : int) : (term158 _69910 _69911) = (term160 _69910 _69911).
Proof. exact (@lem5413733 (term161 _69910) _69911). Qed.
Lemma lem5413736 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5413737 (_69910 : int) : (term164 _69910) = (term165 _69910).
Proof. exact (@lem5413736 (term159 _69910) term166). Qed.
Lemma lem5413739 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5413740 (_69910 : int) : (term167 _69910) = (term168 _69910).
Proof. exact (@lem5413739 _69910 term166). Qed.
Lemma lem5413742 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413743 : term169 = term170.
Proof. exact (@lem5413742 term69). Qed.
Lemma lem5413744 (_69910 : int) : (term171 _69910) = (term171 _69910).
Proof. exact (eq_refl (term171 _69910)). Qed.
Lemma lem5413745 (_69910 : int) : (term168 _69910) = (term172 _69910).
Proof. exact (MK_COMB (@lem5413744 _69910) (@lem5413743)). Qed.
Lemma lem5413746 (_69910 : int) : (term167 _69910) = (term172 _69910).
Proof. exact (TRANS (@lem5413740 _69910) (@lem5413745 _69910)). Qed.
Lemma lem5413747 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5413748 (_69910 : int) : (term173 _69910) = (term174 _69910).
Proof. exact (MK_COMB (@lem5413747) (@lem5413746 _69910)). Qed.
Lemma lem5413750 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413751 : term169 = term170.
Proof. exact (@lem5413750 term69). Qed.
Lemma lem5413752 (_69910 : int) : (term165 _69910) = (term175 _69910).
Proof. exact (MK_COMB (@lem5413748 _69910) (@lem5413751)). Qed.
Lemma lem5413753 (_69910 : int) : (term164 _69910) = (term175 _69910).
Proof. exact (TRANS (@lem5413737 _69910) (@lem5413752 _69910)). Qed.
Lemma lem5413754 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413755 (_69910 : int) : (term176 _69910) = (term177 _69910).
Proof. exact (MK_COMB (@lem5413754) (@lem5413753 _69910)). Qed.
Lemma lem5413756 (_69911 : int) : (real_of_int _69911) = (real_of_int _69911).
Proof. exact (eq_refl (real_of_int _69911)). Qed.
Lemma lem5413757 (_69910 : int) (_69911 : int) : (term160 _69910 _69911) = (term178 _69910 _69911).
Proof. exact (MK_COMB (@lem5413755 _69910) (@lem5413756 _69911)). Qed.
Lemma lem5413758 (_69910 : int) (_69911 : int) : (term158 _69910 _69911) = (term178 _69910 _69911).
Proof. exact (TRANS (@lem5413734 _69910 _69911) (@lem5413757 _69910 _69911)). Qed.
Lemma lem5413759 (_69910 : int) (_69911 : int) : (term115 _69911 _69910) = (term178 _69910 _69911).
Proof. exact (TRANS (@lem5413731 _69910 _69911) (@lem5413758 _69910 _69911)). Qed.
Lemma lem5413760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413761 (_69911 : int) (_69909 : int) : (term183 _69909 _69911) = (term184 _69911 _69909).
Proof. exact (MK_COMB (@lem5413760) (@lem5413728 _69911 _69909)). Qed.
Lemma lem5413762 (_69909 : int) (_69910 : int) (_69911 : int) : (term96 _69909 _69911 _69910) = (term185 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413761 _69911 _69909) (@lem5413759 _69910 _69911)). Qed.
Lemma lem5413765 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413767 (_69909 : int) (_69911 : int) : (int_le _69909 _69911) = (term148 _69909 _69911).
Proof. exact (@lem5413765 _69909 _69911). Qed.
Lemma lem5413770 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413772 (_69911 : int) (_69910 : int) : (int_le _69911 _69910) = (term148 _69911 _69910).
Proof. exact (@lem5413770 _69911 _69910). Qed.
Lemma lem5413773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413774 (_69909 : int) (_69911 : int) : (term100 _69909 _69911) = (term186 _69909 _69911).
Proof. exact (MK_COMB (@lem5413773) (@lem5413767 _69909 _69911)). Qed.
Lemma lem5413775 (_69909 : int) (_69911 : int) (_69910 : int) : (term102 _69909 _69911 _69910) = (term187 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413774 _69909 _69911) (@lem5413772 _69911 _69910)). Qed.
Lemma lem5413776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413777 (_69909 : int) (_69910 : int) (_69911 : int) : (term106 _69909 _69911 _69910) = (term188 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413776) (@lem5413762 _69909 _69910 _69911)). Qed.
Lemma lem5413778 (_69909 : int) (_69911 : int) (_69910 : int) : (term108 _69909 _69911 _69910) = (term189 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413777 _69909 _69910 _69911) (@lem5413775 _69909 _69911 _69910)). Qed.
Lemma lem5413781 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413783 (_69909 : int) (_69911 : int) : (int_le _69909 _69911) = (term148 _69909 _69911).
Proof. exact (@lem5413781 _69909 _69911). Qed.
Lemma lem5413786 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413787 (_69911 : int) (_69910 : int) : (term97 _69911 _69910) = (term190 _69911 _69910).
Proof. exact (@lem5413786 _69911 (term159 _69910)). Qed.
Lemma lem5413789 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5413790 (_69910 : int) : (term167 _69910) = (term168 _69910).
Proof. exact (@lem5413789 _69910 term166). Qed.
Lemma lem5413792 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413793 : term169 = term170.
Proof. exact (@lem5413792 term69). Qed.
Lemma lem5413794 (_69910 : int) : (term171 _69910) = (term171 _69910).
Proof. exact (eq_refl (term171 _69910)). Qed.
Lemma lem5413795 (_69910 : int) : (term168 _69910) = (term172 _69910).
Proof. exact (MK_COMB (@lem5413794 _69910) (@lem5413793)). Qed.
Lemma lem5413796 (_69910 : int) : (term167 _69910) = (term172 _69910).
Proof. exact (TRANS (@lem5413790 _69910) (@lem5413795 _69910)). Qed.
Lemma lem5413797 (_69911 : int) : (term191 _69911) = (term191 _69911).
Proof. exact (eq_refl (term191 _69911)). Qed.
Lemma lem5413798 (_69911 : int) (_69910 : int) : (term190 _69911 _69910) = (term192 _69911 _69910).
Proof. exact (MK_COMB (@lem5413797 _69911) (@lem5413796 _69910)). Qed.
Lemma lem5413800 (_69911 : int) (_69910 : int) : (term97 _69911 _69910) = (term192 _69911 _69910).
Proof. exact (TRANS (@lem5413787 _69911 _69910) (@lem5413798 _69911 _69910)). Qed.
Lemma lem5413801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413802 (_69909 : int) (_69911 : int) : (term100 _69909 _69911) = (term186 _69909 _69911).
Proof. exact (MK_COMB (@lem5413801) (@lem5413783 _69909 _69911)). Qed.
Lemma lem5413803 (_69909 : int) (_69911 : int) (_69910 : int) : (term110 _69909 _69911 _69910) = (term193 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413802 _69909 _69911) (@lem5413800 _69911 _69910)). Qed.
Lemma lem5413805 (y : int) (x : int) : (term104 x y) = (term157 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5413806 (_69911 : int) (_69909 : int) : (term104 _69909 _69911) = (term157 _69911 _69909).
Proof. exact (@lem5413805 _69911 _69909). Qed.
Lemma lem5413808 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413809 (_69911 : int) (_69909 : int) : (term157 _69911 _69909) = (term179 _69911 _69909).
Proof. exact (@lem5413808 (term159 _69911) _69909). Qed.
Lemma lem5413811 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5413812 (_69911 : int) : (term167 _69911) = (term168 _69911).
Proof. exact (@lem5413811 _69911 term166). Qed.
Lemma lem5413814 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413815 : term169 = term170.
Proof. exact (@lem5413814 term69). Qed.
Lemma lem5413816 (_69911 : int) : (term171 _69911) = (term171 _69911).
Proof. exact (eq_refl (term171 _69911)). Qed.
Lemma lem5413817 (_69911 : int) : (term168 _69911) = (term172 _69911).
Proof. exact (MK_COMB (@lem5413816 _69911) (@lem5413815)). Qed.
Lemma lem5413818 (_69911 : int) : (term167 _69911) = (term172 _69911).
Proof. exact (TRANS (@lem5413812 _69911) (@lem5413817 _69911)). Qed.
Lemma lem5413819 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413820 (_69911 : int) : (term180 _69911) = (term181 _69911).
Proof. exact (MK_COMB (@lem5413819) (@lem5413818 _69911)). Qed.
Lemma lem5413821 (_69909 : int) : (real_of_int _69909) = (real_of_int _69909).
Proof. exact (eq_refl (real_of_int _69909)). Qed.
Lemma lem5413822 (_69911 : int) (_69909 : int) : (term179 _69911 _69909) = (term182 _69911 _69909).
Proof. exact (MK_COMB (@lem5413820 _69911) (@lem5413821 _69909)). Qed.
Lemma lem5413823 (_69911 : int) (_69909 : int) : (term157 _69911 _69909) = (term182 _69911 _69909).
Proof. exact (TRANS (@lem5413809 _69911 _69909) (@lem5413822 _69911 _69909)). Qed.
Lemma lem5413824 (_69911 : int) (_69909 : int) : (term104 _69909 _69911) = (term182 _69911 _69909).
Proof. exact (TRANS (@lem5413806 _69911 _69909) (@lem5413823 _69911 _69909)). Qed.
Lemma lem5413826 (y : int) (x : int) : (term104 x y) = (term157 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5413827 (_69910 : int) (_69911 : int) : (term104 _69911 _69910) = (term157 _69910 _69911).
Proof. exact (@lem5413826 _69910 _69911). Qed.
Lemma lem5413829 (x : int) (y : int) : (int_le x y) = (term148 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5413830 (_69910 : int) (_69911 : int) : (term157 _69910 _69911) = (term179 _69910 _69911).
Proof. exact (@lem5413829 (term159 _69910) _69911). Qed.
Lemma lem5413832 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5413833 (_69910 : int) : (term167 _69910) = (term168 _69910).
Proof. exact (@lem5413832 _69910 term166). Qed.
Lemma lem5413835 (n : nat) : (term151 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5413836 : term169 = term170.
Proof. exact (@lem5413835 term69). Qed.
Lemma lem5413837 (_69910 : int) : (term171 _69910) = (term171 _69910).
Proof. exact (eq_refl (term171 _69910)). Qed.
Lemma lem5413838 (_69910 : int) : (term168 _69910) = (term172 _69910).
Proof. exact (MK_COMB (@lem5413837 _69910) (@lem5413836)). Qed.
Lemma lem5413839 (_69910 : int) : (term167 _69910) = (term172 _69910).
Proof. exact (TRANS (@lem5413833 _69910) (@lem5413838 _69910)). Qed.
Lemma lem5413840 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5413841 (_69910 : int) : (term180 _69910) = (term181 _69910).
Proof. exact (MK_COMB (@lem5413840) (@lem5413839 _69910)). Qed.
Lemma lem5413842 (_69911 : int) : (real_of_int _69911) = (real_of_int _69911).
Proof. exact (eq_refl (real_of_int _69911)). Qed.
Lemma lem5413843 (_69910 : int) (_69911 : int) : (term179 _69910 _69911) = (term182 _69910 _69911).
Proof. exact (MK_COMB (@lem5413841 _69910) (@lem5413842 _69911)). Qed.
Lemma lem5413844 (_69910 : int) (_69911 : int) : (term157 _69910 _69911) = (term182 _69910 _69911).
Proof. exact (TRANS (@lem5413830 _69910 _69911) (@lem5413843 _69910 _69911)). Qed.
Lemma lem5413845 (_69910 : int) (_69911 : int) : (term104 _69911 _69910) = (term182 _69910 _69911).
Proof. exact (TRANS (@lem5413827 _69910 _69911) (@lem5413844 _69910 _69911)). Qed.
Lemma lem5413846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413847 (_69911 : int) (_69909 : int) : (term183 _69909 _69911) = (term184 _69911 _69909).
Proof. exact (MK_COMB (@lem5413846) (@lem5413824 _69911 _69909)). Qed.
Lemma lem5413848 (_69909 : int) (_69910 : int) (_69911 : int) : (term111 _69909 _69911 _69910) = (term194 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413847 _69911 _69909) (@lem5413845 _69910 _69911)). Qed.
Lemma lem5413849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413850 (_69909 : int) (_69911 : int) (_69910 : int) : (term118 _69909 _69911 _69910) = (term195 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413849) (@lem5413803 _69909 _69911 _69910)). Qed.
Lemma lem5413851 (_69909 : int) (_69910 : int) (_69911 : int) : (term120 _69909 _69911 _69910) = (term196 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413850 _69909 _69911 _69910) (@lem5413848 _69909 _69910 _69911)). Qed.
Lemma lem5413852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5413853 (_69909 : int) (_69911 : int) (_69910 : int) : (term123 _69909 _69911 _69910) = (term197 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5413852) (@lem5413778 _69909 _69911 _69910)). Qed.
Lemma lem5413854 (_69909 : int) (_69910 : int) (_69911 : int) : (term125 _69909 _69911 _69910) = (term198 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413853 _69909 _69911 _69910) (@lem5413851 _69909 _69910 _69911)). Qed.
Lemma lem5413855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413856 (_69910 : int) (_69909 : int) : (term129 _69909 _69910) = (term199 _69910 _69909).
Proof. exact (MK_COMB (@lem5413855) (@lem5413707 _69910 _69909)). Qed.
Lemma lem5413857 (_69909 : int) (_69910 : int) (_69911 : int) : (term131 _69909 _69911 _69910) = (term200 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413856 _69910 _69909) (@lem5413854 _69909 _69910 _69911)). Qed.
Lemma lem5413858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413859 (_69911 : int) : (term134 _69911) = (term201 _69911).
Proof. exact (MK_COMB (@lem5413858) (@lem5413676 _69911)). Qed.
Lemma lem5413860 (_69909 : int) (_69910 : int) (_69911 : int) : (term136 _69909 _69911 _69910) = (term202 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413859 _69911) (@lem5413857 _69909 _69910 _69911)). Qed.
Lemma lem5413861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413862 (_69910 : int) : (term134 _69910) = (term201 _69910).
Proof. exact (MK_COMB (@lem5413861) (@lem5413663 _69910)). Qed.
Lemma lem5413863 (_69909 : int) (_69910 : int) (_69911 : int) : (term141 _69909 _69911 _69910) = (term203 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413862 _69910) (@lem5413860 _69909 _69910 _69911)). Qed.
Lemma lem5413864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5413865 (_69909 : int) : (term134 _69909) = (term201 _69909).
Proof. exact (MK_COMB (@lem5413864) (@lem5413650 _69909)). Qed.
Lemma lem5413866 (_69909 : int) (_69910 : int) (_69911 : int) : (term145 _69909 _69911 _69910) = (term204 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5413865 _69909) (@lem5413863 _69909 _69910 _69911)). Qed.
Lemma lem5413867 (_69909 : int) (_69910 : int) (_69911 : int) : (term146 _69909 _69911 _69910) = (term204 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5413637 _69909 _69911 _69910) (@lem5413866 _69909 _69910 _69911)). Qed.
Lemma lem5413871 (t : Prop) : (term205 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5413987 (_69909 : int) (_69910 : int) (_69911 : int) : (term206 _69909 _69910 _69911) = (term204 _69909 _69910 _69911).
Proof. exact (@lem5413871 (term204 _69909 _69910 _69911)). Qed.
Lemma lem5413988 (_69909 : int) : (term156 _69909) = (term207 _69909).
Proof. exact (@lem1988287 (real_of_int _69909) term153). Qed.
Lemma lem5413994 (_69909 : int) : (term208 _69909) = (term209 _69909).
Proof. exact (@lem1982792 (real_of_int _69909) term153). Qed.
Lemma lem5413996 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5413997 : term153 = term211.
Proof. exact (@lem5413996 (NUMERAL 0)). Qed.
Lemma lem5413999 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5414000 : term214 = term215.
Proof. exact (@lem5413999 term69). Qed.
Lemma lem5414001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414002 : term216 = term217.
Proof. exact (MK_COMB (@lem5414001) (@lem5414000)). Qed.
Lemma lem5414003 : term218 = term219.
Proof. exact (MK_COMB (@lem5414002) (@lem5413997)). Qed.
Lemma lem5414004 : term219 = term220.
Proof. exact (@lem1981613 term214 term153 term170 term170). Qed.
Lemma lem5414006 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414007 : term223 = term224.
Proof. exact (@lem5414006 term69 term69). Qed.
Lemma lem5414008 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414009 : term226 = term69.
Proof. exact (EQ_MP (@lem5414008) (@lem940073)). Qed.
Lemma lem5414010 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414011 : term224 = term170.
Proof. exact (MK_COMB (@lem5414010) (@lem5414009)). Qed.
Lemma lem5414012 : term223 = term170.
Proof. exact (TRANS (@lem5414007) (@lem5414011)). Qed.
Lemma lem5414014 (x : nat) : (term227 x) = term153.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5414015 : term218 = term153.
Proof. exact (@lem5414014 term69). Qed.
Lemma lem5414016 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5414017 : term228 = term229.
Proof. exact (MK_COMB (@lem5414016) (@lem5414015)). Qed.
Lemma lem5414018 : term220 = term211.
Proof. exact (MK_COMB (@lem5414017) (@lem5414012)). Qed.
Lemma lem5414019 : term219 = term211.
Proof. exact (TRANS (@lem5414004) (@lem5414018)). Qed.
Lemma lem5414020 : term218 = term211.
Proof. exact (TRANS (@lem5414003) (@lem5414019)). Qed.
Lemma lem5414022 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5414023 : term211 = term153.
Proof. exact (@lem5414022 term153). Qed.
Lemma lem5414024 : term218 = term153.
Proof. exact (TRANS (@lem5414020) (@lem5414023)). Qed.
Lemma lem5414025 (_69909 : int) : (term171 _69909) = (term171 _69909).
Proof. exact (eq_refl (term171 _69909)). Qed.
Lemma lem5414026 (_69909 : int) : (term209 _69909) = (term231 _69909).
Proof. exact (MK_COMB (@lem5414025 _69909) (@lem5414024)). Qed.
Lemma lem5414027 (_69909 : int) : (term231 _69909) = (real_of_int _69909).
Proof. exact (@lem1982723 (real_of_int _69909)). Qed.
Lemma lem5414028 (_69909 : int) : (term209 _69909) = (real_of_int _69909).
Proof. exact (TRANS (@lem5414026 _69909) (@lem5414027 _69909)). Qed.
Lemma lem5414030 (_69909 : int) : (term208 _69909) = (real_of_int _69909).
Proof. exact (TRANS (@lem5413994 _69909) (@lem5414028 _69909)). Qed.
Lemma lem5414031 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414032 (_69909 : int) : (term232 _69909) = (term233 _69909).
Proof. exact (MK_COMB (@lem5414031) (@lem5414030 _69909)). Qed.
Lemma lem5414033 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414034 (_69909 : int) : (term207 _69909) = (term234 _69909).
Proof. exact (MK_COMB (@lem5414032 _69909) (@lem5414033)). Qed.
Lemma lem5414035 (_69909 : int) : (term156 _69909) = (term234 _69909).
Proof. exact (TRANS (@lem5413988 _69909) (@lem5414034 _69909)). Qed.
Lemma lem5414036 (_69910 : int) : (term156 _69910) = (term207 _69910).
Proof. exact (@lem1988287 (real_of_int _69910) term153). Qed.
Lemma lem5414042 (_69910 : int) : (term208 _69910) = (term209 _69910).
Proof. exact (@lem1982792 (real_of_int _69910) term153). Qed.
Lemma lem5414044 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414045 : term153 = term211.
Proof. exact (@lem5414044 (NUMERAL 0)). Qed.
Lemma lem5414047 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5414048 : term214 = term215.
Proof. exact (@lem5414047 term69). Qed.
Lemma lem5414049 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414050 : term216 = term217.
Proof. exact (MK_COMB (@lem5414049) (@lem5414048)). Qed.
Lemma lem5414051 : term218 = term219.
Proof. exact (MK_COMB (@lem5414050) (@lem5414045)). Qed.
Lemma lem5414052 : term219 = term220.
Proof. exact (@lem1981613 term214 term153 term170 term170). Qed.
Lemma lem5414054 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414055 : term223 = term224.
Proof. exact (@lem5414054 term69 term69). Qed.
Lemma lem5414056 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414057 : term226 = term69.
Proof. exact (EQ_MP (@lem5414056) (@lem940073)). Qed.
Lemma lem5414058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414059 : term224 = term170.
Proof. exact (MK_COMB (@lem5414058) (@lem5414057)). Qed.
Lemma lem5414060 : term223 = term170.
Proof. exact (TRANS (@lem5414055) (@lem5414059)). Qed.
Lemma lem5414062 (x : nat) : (term227 x) = term153.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5414063 : term218 = term153.
Proof. exact (@lem5414062 term69). Qed.
Lemma lem5414064 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5414065 : term228 = term229.
Proof. exact (MK_COMB (@lem5414064) (@lem5414063)). Qed.
Lemma lem5414066 : term220 = term211.
Proof. exact (MK_COMB (@lem5414065) (@lem5414060)). Qed.
Lemma lem5414067 : term219 = term211.
Proof. exact (TRANS (@lem5414052) (@lem5414066)). Qed.
Lemma lem5414068 : term218 = term211.
Proof. exact (TRANS (@lem5414051) (@lem5414067)). Qed.
Lemma lem5414070 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5414071 : term211 = term153.
Proof. exact (@lem5414070 term153). Qed.
Lemma lem5414072 : term218 = term153.
Proof. exact (TRANS (@lem5414068) (@lem5414071)). Qed.
Lemma lem5414073 (_69910 : int) : (term171 _69910) = (term171 _69910).
Proof. exact (eq_refl (term171 _69910)). Qed.
Lemma lem5414074 (_69910 : int) : (term209 _69910) = (term231 _69910).
Proof. exact (MK_COMB (@lem5414073 _69910) (@lem5414072)). Qed.
Lemma lem5414075 (_69910 : int) : (term231 _69910) = (real_of_int _69910).
Proof. exact (@lem1982723 (real_of_int _69910)). Qed.
Lemma lem5414076 (_69910 : int) : (term209 _69910) = (real_of_int _69910).
Proof. exact (TRANS (@lem5414074 _69910) (@lem5414075 _69910)). Qed.
Lemma lem5414078 (_69910 : int) : (term208 _69910) = (real_of_int _69910).
Proof. exact (TRANS (@lem5414042 _69910) (@lem5414076 _69910)). Qed.
Lemma lem5414079 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414080 (_69910 : int) : (term232 _69910) = (term233 _69910).
Proof. exact (MK_COMB (@lem5414079) (@lem5414078 _69910)). Qed.
Lemma lem5414081 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414082 (_69910 : int) : (term207 _69910) = (term234 _69910).
Proof. exact (MK_COMB (@lem5414080 _69910) (@lem5414081)). Qed.
Lemma lem5414083 (_69910 : int) : (term156 _69910) = (term234 _69910).
Proof. exact (TRANS (@lem5414036 _69910) (@lem5414082 _69910)). Qed.
Lemma lem5414084 (_69911 : int) : (term156 _69911) = (term207 _69911).
Proof. exact (@lem1988287 (real_of_int _69911) term153). Qed.
Lemma lem5414090 (_69911 : int) : (term208 _69911) = (term209 _69911).
Proof. exact (@lem1982792 (real_of_int _69911) term153). Qed.
Lemma lem5414092 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414093 : term153 = term211.
Proof. exact (@lem5414092 (NUMERAL 0)). Qed.
Lemma lem5414095 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5414096 : term214 = term215.
Proof. exact (@lem5414095 term69). Qed.
Lemma lem5414097 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414098 : term216 = term217.
Proof. exact (MK_COMB (@lem5414097) (@lem5414096)). Qed.
Lemma lem5414099 : term218 = term219.
Proof. exact (MK_COMB (@lem5414098) (@lem5414093)). Qed.
Lemma lem5414100 : term219 = term220.
Proof. exact (@lem1981613 term214 term153 term170 term170). Qed.
Lemma lem5414102 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414103 : term223 = term224.
Proof. exact (@lem5414102 term69 term69). Qed.
Lemma lem5414104 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414105 : term226 = term69.
Proof. exact (EQ_MP (@lem5414104) (@lem940073)). Qed.
Lemma lem5414106 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414107 : term224 = term170.
Proof. exact (MK_COMB (@lem5414106) (@lem5414105)). Qed.
Lemma lem5414108 : term223 = term170.
Proof. exact (TRANS (@lem5414103) (@lem5414107)). Qed.
Lemma lem5414110 (x : nat) : (term227 x) = term153.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5414111 : term218 = term153.
Proof. exact (@lem5414110 term69). Qed.
Lemma lem5414112 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5414113 : term228 = term229.
Proof. exact (MK_COMB (@lem5414112) (@lem5414111)). Qed.
Lemma lem5414114 : term220 = term211.
Proof. exact (MK_COMB (@lem5414113) (@lem5414108)). Qed.
Lemma lem5414115 : term219 = term211.
Proof. exact (TRANS (@lem5414100) (@lem5414114)). Qed.
Lemma lem5414116 : term218 = term211.
Proof. exact (TRANS (@lem5414099) (@lem5414115)). Qed.
Lemma lem5414118 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5414119 : term211 = term153.
Proof. exact (@lem5414118 term153). Qed.
Lemma lem5414120 : term218 = term153.
Proof. exact (TRANS (@lem5414116) (@lem5414119)). Qed.
Lemma lem5414121 (_69911 : int) : (term171 _69911) = (term171 _69911).
Proof. exact (eq_refl (term171 _69911)). Qed.
Lemma lem5414122 (_69911 : int) : (term209 _69911) = (term231 _69911).
Proof. exact (MK_COMB (@lem5414121 _69911) (@lem5414120)). Qed.
Lemma lem5414123 (_69911 : int) : (term231 _69911) = (real_of_int _69911).
Proof. exact (@lem1982723 (real_of_int _69911)). Qed.
Lemma lem5414124 (_69911 : int) : (term209 _69911) = (real_of_int _69911).
Proof. exact (TRANS (@lem5414122 _69911) (@lem5414123 _69911)). Qed.
Lemma lem5414126 (_69911 : int) : (term208 _69911) = (real_of_int _69911).
Proof. exact (TRANS (@lem5414090 _69911) (@lem5414124 _69911)). Qed.
Lemma lem5414127 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414128 (_69911 : int) : (term232 _69911) = (term233 _69911).
Proof. exact (MK_COMB (@lem5414127) (@lem5414126 _69911)). Qed.
Lemma lem5414129 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414130 (_69911 : int) : (term207 _69911) = (term234 _69911).
Proof. exact (MK_COMB (@lem5414128 _69911) (@lem5414129)). Qed.
Lemma lem5414131 (_69911 : int) : (term156 _69911) = (term234 _69911).
Proof. exact (TRANS (@lem5414084 _69911) (@lem5414130 _69911)). Qed.
Lemma lem5414132 (_69909 : int) (_69910 : int) : (term178 _69910 _69909) = (term235 _69909 _69910).
Proof. exact (@lem1988287 (real_of_int _69909) (term175 _69910)). Qed.
Lemma lem5414144 (_69910 : int) : (term175 _69910) = (term236 _69910).
Proof. exact (@lem1982755 (real_of_int _69910) term170 term170). Qed.
Lemma lem5414146 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414147 : term170 = term237.
Proof. exact (@lem5414146 term69). Qed.
Lemma lem5414149 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414150 : term170 = term237.
Proof. exact (@lem5414149 term69). Qed.
Lemma lem5414151 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5414152 : term238 = term239.
Proof. exact (MK_COMB (@lem5414151) (@lem5414150)). Qed.
Lemma lem5414153 : term240 = term241.
Proof. exact (MK_COMB (@lem5414152) (@lem5414147)). Qed.
Lemma lem5414154 : term242.
Proof. exact (@lem1981473 term170 term170 term170 term170 term243 term170). Qed.
Lemma lem5414156 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5414157 : term245 = term246.
Proof. exact (@lem5414156 (NUMERAL 0) term69). Qed.
Lemma lem5414158 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5414159 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5414160 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5414159 h1) (fun h1 : term246 = True => @lem5414158)). Qed.
Lemma lem5414161 : term246 = True.
Proof. exact (EQ_MP (@lem5414160) (@lem5414158)). Qed.
Lemma lem5414162 : term245 = True.
Proof. exact (TRANS (@lem5414157) (@lem5414161)). Qed.
Lemma lem5414163 : True = term245.
Proof. exact (SYM (@lem5414162)). Qed.
Lemma lem5414164 : term245.
Proof. exact (EQ_MP (@lem5414163) (@lem0)). Qed.
Lemma lem5414165 : term248.
Proof. exact (@lem5414154 (@lem5414164)). Qed.
Lemma lem5414167 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5414168 : term245 = term246.
Proof. exact (@lem5414167 (NUMERAL 0) term69). Qed.
Lemma lem5414169 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5414170 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5414171 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5414170 h1) (fun h1 : term246 = True => @lem5414169)). Qed.
Lemma lem5414172 : term246 = True.
Proof. exact (EQ_MP (@lem5414171) (@lem5414169)). Qed.
Lemma lem5414173 : term245 = True.
Proof. exact (TRANS (@lem5414168) (@lem5414172)). Qed.
Lemma lem5414174 : True = term245.
Proof. exact (SYM (@lem5414173)). Qed.
Lemma lem5414175 : term245.
Proof. exact (EQ_MP (@lem5414174) (@lem0)). Qed.
Lemma lem5414176 : term249.
Proof. exact (@lem5414165 (@lem5414175)). Qed.
Lemma lem5414178 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5414179 : term245 = term246.
Proof. exact (@lem5414178 (NUMERAL 0) term69). Qed.
Lemma lem5414180 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5414181 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5414182 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5414181 h1) (fun h1 : term246 = True => @lem5414180)). Qed.
Lemma lem5414183 : term246 = True.
Proof. exact (EQ_MP (@lem5414182) (@lem5414180)). Qed.
Lemma lem5414184 : term245 = True.
Proof. exact (TRANS (@lem5414179) (@lem5414183)). Qed.
Lemma lem5414185 : True = term245.
Proof. exact (SYM (@lem5414184)). Qed.
Lemma lem5414186 : term245.
Proof. exact (EQ_MP (@lem5414185) (@lem0)). Qed.
Lemma lem5414187 : term250.
Proof. exact (@lem5414176 (@lem5414186)). Qed.
Lemma lem5414189 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414190 : term223 = term224.
Proof. exact (@lem5414189 term69 term69). Qed.
Lemma lem5414191 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414192 : term226 = term69.
Proof. exact (EQ_MP (@lem5414191) (@lem940073)). Qed.
Lemma lem5414193 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414194 : term224 = term170.
Proof. exact (MK_COMB (@lem5414193) (@lem5414192)). Qed.
Lemma lem5414195 : term223 = term170.
Proof. exact (TRANS (@lem5414190) (@lem5414194)). Qed.
Lemma lem5414197 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414198 : term223 = term224.
Proof. exact (@lem5414197 term69 term69). Qed.
Lemma lem5414199 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414200 : term226 = term69.
Proof. exact (EQ_MP (@lem5414199) (@lem940073)). Qed.
Lemma lem5414201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414202 : term224 = term170.
Proof. exact (MK_COMB (@lem5414201) (@lem5414200)). Qed.
Lemma lem5414203 : term223 = term170.
Proof. exact (TRANS (@lem5414198) (@lem5414202)). Qed.
Lemma lem5414204 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5414205 : term251 = term238.
Proof. exact (MK_COMB (@lem5414204) (@lem5414203)). Qed.
Lemma lem5414206 : term252 = term240.
Proof. exact (MK_COMB (@lem5414205) (@lem5414195)). Qed.
Lemma lem5414207 : term240 = term253.
Proof. exact (@lem1367770 term69 term69). Qed.
Lemma lem5414208 : term254 = term255.
Proof. exact (@lem706885). Qed.
Lemma lem5414209 : (term254 = term255) = (term256 = term257).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term255). Qed.
Lemma lem5414210 : term256 = term257.
Proof. exact (EQ_MP (@lem5414209) (@lem5414208)). Qed.
Lemma lem5414211 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414212 : term253 = term243.
Proof. exact (MK_COMB (@lem5414211) (@lem5414210)). Qed.
Lemma lem5414213 : term240 = term243.
Proof. exact (TRANS (@lem5414207) (@lem5414212)). Qed.
Lemma lem5414214 : term252 = term243.
Proof. exact (TRANS (@lem5414206) (@lem5414213)). Qed.
Lemma lem5414215 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414216 : term258 = term259.
Proof. exact (MK_COMB (@lem5414215) (@lem5414214)). Qed.
Lemma lem5414217 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5414218 : term260 = term261.
Proof. exact (MK_COMB (@lem5414216) (@lem5414217)). Qed.
Lemma lem5414220 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414221 : term261 = term262.
Proof. exact (@lem5414220 term257 term69). Qed.
Lemma lem5414222 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5414223 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5414224 : term264 = term257.
Proof. exact (EQ_MP (@lem5414223) (@lem5414222)). Qed.
Lemma lem5414225 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414226 : term262 = term243.
Proof. exact (MK_COMB (@lem5414225) (@lem5414224)). Qed.
Lemma lem5414227 : term261 = term243.
Proof. exact (TRANS (@lem5414221) (@lem5414226)). Qed.
Lemma lem5414228 : term260 = term243.
Proof. exact (TRANS (@lem5414218) (@lem5414227)). Qed.
Lemma lem5414230 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414231 : term223 = term224.
Proof. exact (@lem5414230 term69 term69). Qed.
Lemma lem5414232 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414233 : term226 = term69.
Proof. exact (EQ_MP (@lem5414232) (@lem940073)). Qed.
Lemma lem5414234 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414235 : term224 = term170.
Proof. exact (MK_COMB (@lem5414234) (@lem5414233)). Qed.
Lemma lem5414236 : term223 = term170.
Proof. exact (TRANS (@lem5414231) (@lem5414235)). Qed.
Lemma lem5414237 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem5414238 : term265 = term261.
Proof. exact (MK_COMB (@lem5414237) (@lem5414236)). Qed.
Lemma lem5414240 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414241 : term261 = term262.
Proof. exact (@lem5414240 term257 term69). Qed.
Lemma lem5414242 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5414243 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5414244 : term264 = term257.
Proof. exact (EQ_MP (@lem5414243) (@lem5414242)). Qed.
Lemma lem5414245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414246 : term262 = term243.
Proof. exact (MK_COMB (@lem5414245) (@lem5414244)). Qed.
Lemma lem5414247 : term261 = term243.
Proof. exact (TRANS (@lem5414241) (@lem5414246)). Qed.
Lemma lem5414248 : term265 = term243.
Proof. exact (TRANS (@lem5414238) (@lem5414247)). Qed.
Lemma lem5414249 : term243 = term265.
Proof. exact (SYM (@lem5414248)). Qed.
Lemma lem5414250 : term260 = term265.
Proof. exact (TRANS (@lem5414228) (@lem5414249)). Qed.
Lemma lem5414251 : term241 = term266.
Proof. exact (@lem5414187 (@lem5414250)). Qed.
Lemma lem5414252 : term240 = term266.
Proof. exact (TRANS (@lem5414153) (@lem5414251)). Qed.
Lemma lem5414254 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5414255 : term266 = term243.
Proof. exact (@lem5414254 term243). Qed.
Lemma lem5414256 : term240 = term243.
Proof. exact (TRANS (@lem5414252) (@lem5414255)). Qed.
Lemma lem5414257 (_69910 : int) : (term171 _69910) = (term171 _69910).
Proof. exact (eq_refl (term171 _69910)). Qed.
Lemma lem5414258 (_69910 : int) : (term236 _69910) = (term267 _69910).
Proof. exact (MK_COMB (@lem5414257 _69910) (@lem5414256)). Qed.
Lemma lem5414260 (_69910 : int) : (term175 _69910) = (term267 _69910).
Proof. exact (TRANS (@lem5414144 _69910) (@lem5414258 _69910)). Qed.
Lemma lem5414263 (_69909 : int) : (term268 _69909) = (term268 _69909).
Proof. exact (eq_refl (term268 _69909)). Qed.
Lemma lem5414264 (_69909 : int) (_69910 : int) : (term269 _69909 _69910) = (term270 _69909 _69910).
Proof. exact (MK_COMB (@lem5414263 _69909) (@lem5414260 _69910)). Qed.
Lemma lem5414265 (_69909 : int) (_69910 : int) : (term270 _69909 _69910) = (term271 _69909 _69910).
Proof. exact (@lem1982792 (real_of_int _69909) (term267 _69910)). Qed.
Lemma lem5414266 (_69910 : int) : (term272 _69910) = (term273 _69910).
Proof. exact (@lem1982781 (real_of_int _69910) term214 term243). Qed.
Lemma lem5414268 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414269 : term243 = term266.
Proof. exact (@lem5414268 term257). Qed.
Lemma lem5414271 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5414272 : term214 = term215.
Proof. exact (@lem5414271 term69). Qed.
Lemma lem5414273 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414274 : term216 = term217.
Proof. exact (MK_COMB (@lem5414273) (@lem5414272)). Qed.
Lemma lem5414275 : term274 = term275.
Proof. exact (MK_COMB (@lem5414274) (@lem5414269)). Qed.
Lemma lem5414276 : term275 = term276.
Proof. exact (@lem1981613 term214 term243 term170 term170). Qed.
Lemma lem5414278 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414279 : term223 = term224.
Proof. exact (@lem5414278 term69 term69). Qed.
Lemma lem5414280 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414281 : term226 = term69.
Proof. exact (EQ_MP (@lem5414280) (@lem940073)). Qed.
Lemma lem5414282 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414283 : term224 = term170.
Proof. exact (MK_COMB (@lem5414282) (@lem5414281)). Qed.
Lemma lem5414284 : term223 = term170.
Proof. exact (TRANS (@lem5414279) (@lem5414283)). Qed.
Lemma lem5414286 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5414287 : term274 = term279.
Proof. exact (@lem5414286 term69 term257). Qed.
Lemma lem5414288 : term280 = term255.
Proof. exact (@lem996238 term255). Qed.
Lemma lem5414289 : (term280 = term255) = (term281 = term257).
Proof. exact (@lem1007663 (BIT1 0) term255 term255). Qed.
Lemma lem5414290 : term281 = term257.
Proof. exact (EQ_MP (@lem5414289) (@lem5414288)). Qed.
Lemma lem5414291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414292 : term282 = term243.
Proof. exact (MK_COMB (@lem5414291) (@lem5414290)). Qed.
Lemma lem5414293 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5414294 : term279 = term283.
Proof. exact (MK_COMB (@lem5414293) (@lem5414292)). Qed.
Lemma lem5414295 : term274 = term283.
Proof. exact (TRANS (@lem5414287) (@lem5414294)). Qed.
Lemma lem5414296 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5414297 : term284 = term285.
Proof. exact (MK_COMB (@lem5414296) (@lem5414295)). Qed.
Lemma lem5414298 : term276 = term286.
Proof. exact (MK_COMB (@lem5414297) (@lem5414284)). Qed.
Lemma lem5414299 : term275 = term286.
Proof. exact (TRANS (@lem5414276) (@lem5414298)). Qed.
Lemma lem5414300 : term274 = term286.
Proof. exact (TRANS (@lem5414275) (@lem5414299)). Qed.
Lemma lem5414302 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5414303 : term286 = term283.
Proof. exact (@lem5414302 term283). Qed.
Lemma lem5414304 : term274 = term283.
Proof. exact (TRANS (@lem5414300) (@lem5414303)). Qed.
Lemma lem5414307 (_69910 : int) : (term287 _69910) = (term287 _69910).
Proof. exact (eq_refl (term287 _69910)). Qed.
Lemma lem5414308 (_69910 : int) : (term273 _69910) = (term288 _69910).
Proof. exact (MK_COMB (@lem5414307 _69910) (@lem5414304)). Qed.
Lemma lem5414309 (_69910 : int) : (term272 _69910) = (term288 _69910).
Proof. exact (TRANS (@lem5414266 _69910) (@lem5414308 _69910)). Qed.
Lemma lem5414310 (_69909 : int) : (term171 _69909) = (term171 _69909).
Proof. exact (eq_refl (term171 _69909)). Qed.
Lemma lem5414313 (_69909 : int) (_69910 : int) : (term271 _69909 _69910) = (term289 _69909 _69910).
Proof. exact (MK_COMB (@lem5414310 _69909) (@lem5414309 _69910)). Qed.
Lemma lem5414314 (_69909 : int) (_69910 : int) : (term270 _69909 _69910) = (term289 _69909 _69910).
Proof. exact (TRANS (@lem5414265 _69909 _69910) (@lem5414313 _69909 _69910)). Qed.
Lemma lem5414315 (_69909 : int) (_69910 : int) : (term269 _69909 _69910) = (term289 _69909 _69910).
Proof. exact (TRANS (@lem5414264 _69909 _69910) (@lem5414314 _69909 _69910)). Qed.
Lemma lem5414316 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414317 (_69909 : int) (_69910 : int) : (term290 _69909 _69910) = (term291 _69909 _69910).
Proof. exact (MK_COMB (@lem5414316) (@lem5414315 _69909 _69910)). Qed.
Lemma lem5414318 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414319 (_69909 : int) (_69910 : int) : (term235 _69909 _69910) = (term292 _69909 _69910).
Proof. exact (MK_COMB (@lem5414317 _69909 _69910) (@lem5414318)). Qed.
Lemma lem5414320 (_69909 : int) (_69910 : int) : (term178 _69910 _69909) = (term292 _69909 _69910).
Proof. exact (TRANS (@lem5414132 _69909 _69910) (@lem5414319 _69909 _69910)). Qed.
Lemma lem5414321 (_69909 : int) (_69911 : int) : (term182 _69911 _69909) = (term293 _69909 _69911).
Proof. exact (@lem1988287 (real_of_int _69909) (term172 _69911)). Qed.
Lemma lem5414333 (_69909 : int) (_69911 : int) : (term294 _69909 _69911) = (term295 _69909 _69911).
Proof. exact (@lem1982792 (real_of_int _69909) (term172 _69911)). Qed.
Lemma lem5414334 (_69911 : int) : (term296 _69911) = (term297 _69911).
Proof. exact (@lem1982781 (real_of_int _69911) term214 term170). Qed.
Lemma lem5414336 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414337 : term170 = term237.
Proof. exact (@lem5414336 term69). Qed.
Lemma lem5414339 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5414340 : term214 = term215.
Proof. exact (@lem5414339 term69). Qed.
Lemma lem5414341 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414342 : term216 = term217.
Proof. exact (MK_COMB (@lem5414341) (@lem5414340)). Qed.
Lemma lem5414343 : term298 = term299.
Proof. exact (MK_COMB (@lem5414342) (@lem5414337)). Qed.
Lemma lem5414344 : term299 = term300.
Proof. exact (@lem1981613 term214 term170 term170 term170). Qed.
Lemma lem5414346 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414347 : term223 = term224.
Proof. exact (@lem5414346 term69 term69). Qed.
Lemma lem5414348 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414349 : term226 = term69.
Proof. exact (EQ_MP (@lem5414348) (@lem940073)). Qed.
Lemma lem5414350 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414351 : term224 = term170.
Proof. exact (MK_COMB (@lem5414350) (@lem5414349)). Qed.
Lemma lem5414352 : term223 = term170.
Proof. exact (TRANS (@lem5414347) (@lem5414351)). Qed.
Lemma lem5414354 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5414355 : term298 = term301.
Proof. exact (@lem5414354 term69 term69). Qed.
Lemma lem5414356 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414357 : term226 = term69.
Proof. exact (EQ_MP (@lem5414356) (@lem940073)). Qed.
Lemma lem5414358 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414359 : term224 = term170.
Proof. exact (MK_COMB (@lem5414358) (@lem5414357)). Qed.
Lemma lem5414360 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5414361 : term301 = term214.
Proof. exact (MK_COMB (@lem5414360) (@lem5414359)). Qed.
Lemma lem5414362 : term298 = term214.
Proof. exact (TRANS (@lem5414355) (@lem5414361)). Qed.
Lemma lem5414363 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5414364 : term302 = term303.
Proof. exact (MK_COMB (@lem5414363) (@lem5414362)). Qed.
Lemma lem5414365 : term300 = term215.
Proof. exact (MK_COMB (@lem5414364) (@lem5414352)). Qed.
Lemma lem5414366 : term299 = term215.
Proof. exact (TRANS (@lem5414344) (@lem5414365)). Qed.
Lemma lem5414367 : term298 = term215.
Proof. exact (TRANS (@lem5414343) (@lem5414366)). Qed.
Lemma lem5414369 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5414370 : term215 = term214.
Proof. exact (@lem5414369 term214). Qed.
Lemma lem5414371 : term298 = term214.
Proof. exact (TRANS (@lem5414367) (@lem5414370)). Qed.
Lemma lem5414374 (_69911 : int) : (term287 _69911) = (term287 _69911).
Proof. exact (eq_refl (term287 _69911)). Qed.
Lemma lem5414375 (_69911 : int) : (term297 _69911) = (term304 _69911).
Proof. exact (MK_COMB (@lem5414374 _69911) (@lem5414371)). Qed.
Lemma lem5414376 (_69911 : int) : (term296 _69911) = (term304 _69911).
Proof. exact (TRANS (@lem5414334 _69911) (@lem5414375 _69911)). Qed.
Lemma lem5414377 (_69909 : int) : (term171 _69909) = (term171 _69909).
Proof. exact (eq_refl (term171 _69909)). Qed.
Lemma lem5414380 (_69909 : int) (_69911 : int) : (term295 _69909 _69911) = (term305 _69909 _69911).
Proof. exact (MK_COMB (@lem5414377 _69909) (@lem5414376 _69911)). Qed.
Lemma lem5414382 (_69909 : int) (_69911 : int) : (term294 _69909 _69911) = (term305 _69909 _69911).
Proof. exact (TRANS (@lem5414333 _69909 _69911) (@lem5414380 _69909 _69911)). Qed.
Lemma lem5414383 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414384 (_69909 : int) (_69911 : int) : (term306 _69909 _69911) = (term307 _69909 _69911).
Proof. exact (MK_COMB (@lem5414383) (@lem5414382 _69909 _69911)). Qed.
Lemma lem5414385 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414386 (_69909 : int) (_69911 : int) : (term293 _69909 _69911) = (term308 _69909 _69911).
Proof. exact (MK_COMB (@lem5414384 _69909 _69911) (@lem5414385)). Qed.
Lemma lem5414387 (_69909 : int) (_69911 : int) : (term182 _69911 _69909) = (term308 _69909 _69911).
Proof. exact (TRANS (@lem5414321 _69909 _69911) (@lem5414386 _69909 _69911)). Qed.
Lemma lem5414388 (_69911 : int) (_69910 : int) : (term178 _69910 _69911) = (term235 _69911 _69910).
Proof. exact (@lem1988287 (real_of_int _69911) (term175 _69910)). Qed.
Lemma lem5414400 (_69910 : int) : (term175 _69910) = (term236 _69910).
Proof. exact (@lem1982755 (real_of_int _69910) term170 term170). Qed.
Lemma lem5414402 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414403 : term170 = term237.
Proof. exact (@lem5414402 term69). Qed.
Lemma lem5414405 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414406 : term170 = term237.
Proof. exact (@lem5414405 term69). Qed.
Lemma lem5414407 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5414408 : term238 = term239.
Proof. exact (MK_COMB (@lem5414407) (@lem5414406)). Qed.
Lemma lem5414409 : term240 = term241.
Proof. exact (MK_COMB (@lem5414408) (@lem5414403)). Qed.
Lemma lem5414410 : term242.
Proof. exact (@lem1981473 term170 term170 term170 term170 term243 term170). Qed.
Lemma lem5414412 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5414413 : term245 = term246.
Proof. exact (@lem5414412 (NUMERAL 0) term69). Qed.
Lemma lem5414414 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5414415 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5414416 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5414415 h1) (fun h1 : term246 = True => @lem5414414)). Qed.
Lemma lem5414417 : term246 = True.
Proof. exact (EQ_MP (@lem5414416) (@lem5414414)). Qed.
Lemma lem5414418 : term245 = True.
Proof. exact (TRANS (@lem5414413) (@lem5414417)). Qed.
Lemma lem5414419 : True = term245.
Proof. exact (SYM (@lem5414418)). Qed.
Lemma lem5414420 : term245.
Proof. exact (EQ_MP (@lem5414419) (@lem0)). Qed.
Lemma lem5414421 : term248.
Proof. exact (@lem5414410 (@lem5414420)). Qed.
Lemma lem5414423 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5414424 : term245 = term246.
Proof. exact (@lem5414423 (NUMERAL 0) term69). Qed.
Lemma lem5414425 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5414426 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5414427 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5414426 h1) (fun h1 : term246 = True => @lem5414425)). Qed.
Lemma lem5414428 : term246 = True.
Proof. exact (EQ_MP (@lem5414427) (@lem5414425)). Qed.
Lemma lem5414429 : term245 = True.
Proof. exact (TRANS (@lem5414424) (@lem5414428)). Qed.
Lemma lem5414430 : True = term245.
Proof. exact (SYM (@lem5414429)). Qed.
Lemma lem5414431 : term245.
Proof. exact (EQ_MP (@lem5414430) (@lem0)). Qed.
Lemma lem5414432 : term249.
Proof. exact (@lem5414421 (@lem5414431)). Qed.
Lemma lem5414434 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5414435 : term245 = term246.
Proof. exact (@lem5414434 (NUMERAL 0) term69). Qed.
Lemma lem5414436 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5414437 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5414438 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5414437 h1) (fun h1 : term246 = True => @lem5414436)). Qed.
Lemma lem5414439 : term246 = True.
Proof. exact (EQ_MP (@lem5414438) (@lem5414436)). Qed.
Lemma lem5414440 : term245 = True.
Proof. exact (TRANS (@lem5414435) (@lem5414439)). Qed.
Lemma lem5414441 : True = term245.
Proof. exact (SYM (@lem5414440)). Qed.
Lemma lem5414442 : term245.
Proof. exact (EQ_MP (@lem5414441) (@lem0)). Qed.
Lemma lem5414443 : term250.
Proof. exact (@lem5414432 (@lem5414442)). Qed.
Lemma lem5414445 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414446 : term223 = term224.
Proof. exact (@lem5414445 term69 term69). Qed.
Lemma lem5414447 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414448 : term226 = term69.
Proof. exact (EQ_MP (@lem5414447) (@lem940073)). Qed.
Lemma lem5414449 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414450 : term224 = term170.
Proof. exact (MK_COMB (@lem5414449) (@lem5414448)). Qed.
Lemma lem5414451 : term223 = term170.
Proof. exact (TRANS (@lem5414446) (@lem5414450)). Qed.
Lemma lem5414453 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414454 : term223 = term224.
Proof. exact (@lem5414453 term69 term69). Qed.
Lemma lem5414455 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414456 : term226 = term69.
Proof. exact (EQ_MP (@lem5414455) (@lem940073)). Qed.
Lemma lem5414457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414458 : term224 = term170.
Proof. exact (MK_COMB (@lem5414457) (@lem5414456)). Qed.
Lemma lem5414459 : term223 = term170.
Proof. exact (TRANS (@lem5414454) (@lem5414458)). Qed.
Lemma lem5414460 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5414461 : term251 = term238.
Proof. exact (MK_COMB (@lem5414460) (@lem5414459)). Qed.
Lemma lem5414462 : term252 = term240.
Proof. exact (MK_COMB (@lem5414461) (@lem5414451)). Qed.
Lemma lem5414463 : term240 = term253.
Proof. exact (@lem1367770 term69 term69). Qed.
Lemma lem5414464 : term254 = term255.
Proof. exact (@lem706885). Qed.
Lemma lem5414465 : (term254 = term255) = (term256 = term257).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term255). Qed.
Lemma lem5414466 : term256 = term257.
Proof. exact (EQ_MP (@lem5414465) (@lem5414464)). Qed.
Lemma lem5414467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414468 : term253 = term243.
Proof. exact (MK_COMB (@lem5414467) (@lem5414466)). Qed.
Lemma lem5414469 : term240 = term243.
Proof. exact (TRANS (@lem5414463) (@lem5414468)). Qed.
Lemma lem5414470 : term252 = term243.
Proof. exact (TRANS (@lem5414462) (@lem5414469)). Qed.
Lemma lem5414471 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414472 : term258 = term259.
Proof. exact (MK_COMB (@lem5414471) (@lem5414470)). Qed.
Lemma lem5414473 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5414474 : term260 = term261.
Proof. exact (MK_COMB (@lem5414472) (@lem5414473)). Qed.
Lemma lem5414476 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414477 : term261 = term262.
Proof. exact (@lem5414476 term257 term69). Qed.
Lemma lem5414478 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5414479 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5414480 : term264 = term257.
Proof. exact (EQ_MP (@lem5414479) (@lem5414478)). Qed.
Lemma lem5414481 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414482 : term262 = term243.
Proof. exact (MK_COMB (@lem5414481) (@lem5414480)). Qed.
Lemma lem5414483 : term261 = term243.
Proof. exact (TRANS (@lem5414477) (@lem5414482)). Qed.
Lemma lem5414484 : term260 = term243.
Proof. exact (TRANS (@lem5414474) (@lem5414483)). Qed.
Lemma lem5414486 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414487 : term223 = term224.
Proof. exact (@lem5414486 term69 term69). Qed.
Lemma lem5414488 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414489 : term226 = term69.
Proof. exact (EQ_MP (@lem5414488) (@lem940073)). Qed.
Lemma lem5414490 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414491 : term224 = term170.
Proof. exact (MK_COMB (@lem5414490) (@lem5414489)). Qed.
Lemma lem5414492 : term223 = term170.
Proof. exact (TRANS (@lem5414487) (@lem5414491)). Qed.
Lemma lem5414493 : term259 = term259.
Proof. exact (eq_refl term259). Qed.
Lemma lem5414494 : term265 = term261.
Proof. exact (MK_COMB (@lem5414493) (@lem5414492)). Qed.
Lemma lem5414496 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414497 : term261 = term262.
Proof. exact (@lem5414496 term257 term69). Qed.
Lemma lem5414498 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5414499 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5414500 : term264 = term257.
Proof. exact (EQ_MP (@lem5414499) (@lem5414498)). Qed.
Lemma lem5414501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414502 : term262 = term243.
Proof. exact (MK_COMB (@lem5414501) (@lem5414500)). Qed.
Lemma lem5414503 : term261 = term243.
Proof. exact (TRANS (@lem5414497) (@lem5414502)). Qed.
Lemma lem5414504 : term265 = term243.
Proof. exact (TRANS (@lem5414494) (@lem5414503)). Qed.
Lemma lem5414505 : term243 = term265.
Proof. exact (SYM (@lem5414504)). Qed.
Lemma lem5414506 : term260 = term265.
Proof. exact (TRANS (@lem5414484) (@lem5414505)). Qed.
Lemma lem5414507 : term241 = term266.
Proof. exact (@lem5414443 (@lem5414506)). Qed.
Lemma lem5414508 : term240 = term266.
Proof. exact (TRANS (@lem5414409) (@lem5414507)). Qed.
Lemma lem5414510 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5414511 : term266 = term243.
Proof. exact (@lem5414510 term243). Qed.
Lemma lem5414512 : term240 = term243.
Proof. exact (TRANS (@lem5414508) (@lem5414511)). Qed.
Lemma lem5414513 (_69910 : int) : (term171 _69910) = (term171 _69910).
Proof. exact (eq_refl (term171 _69910)). Qed.
Lemma lem5414514 (_69910 : int) : (term236 _69910) = (term267 _69910).
Proof. exact (MK_COMB (@lem5414513 _69910) (@lem5414512)). Qed.
Lemma lem5414516 (_69910 : int) : (term175 _69910) = (term267 _69910).
Proof. exact (TRANS (@lem5414400 _69910) (@lem5414514 _69910)). Qed.
Lemma lem5414519 (_69911 : int) : (term268 _69911) = (term268 _69911).
Proof. exact (eq_refl (term268 _69911)). Qed.
Lemma lem5414520 (_69911 : int) (_69910 : int) : (term269 _69911 _69910) = (term270 _69911 _69910).
Proof. exact (MK_COMB (@lem5414519 _69911) (@lem5414516 _69910)). Qed.
Lemma lem5414521 (_69911 : int) (_69910 : int) : (term270 _69911 _69910) = (term271 _69911 _69910).
Proof. exact (@lem1982792 (real_of_int _69911) (term267 _69910)). Qed.
Lemma lem5414522 (_69910 : int) : (term272 _69910) = (term273 _69910).
Proof. exact (@lem1982781 (real_of_int _69910) term214 term243). Qed.
Lemma lem5414524 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414525 : term243 = term266.
Proof. exact (@lem5414524 term257). Qed.
Lemma lem5414527 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5414528 : term214 = term215.
Proof. exact (@lem5414527 term69). Qed.
Lemma lem5414529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414530 : term216 = term217.
Proof. exact (MK_COMB (@lem5414529) (@lem5414528)). Qed.
Lemma lem5414531 : term274 = term275.
Proof. exact (MK_COMB (@lem5414530) (@lem5414525)). Qed.
Lemma lem5414532 : term275 = term276.
Proof. exact (@lem1981613 term214 term243 term170 term170). Qed.
Lemma lem5414534 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414535 : term223 = term224.
Proof. exact (@lem5414534 term69 term69). Qed.
Lemma lem5414536 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414537 : term226 = term69.
Proof. exact (EQ_MP (@lem5414536) (@lem940073)). Qed.
Lemma lem5414538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414539 : term224 = term170.
Proof. exact (MK_COMB (@lem5414538) (@lem5414537)). Qed.
Lemma lem5414540 : term223 = term170.
Proof. exact (TRANS (@lem5414535) (@lem5414539)). Qed.
Lemma lem5414542 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5414543 : term274 = term279.
Proof. exact (@lem5414542 term69 term257). Qed.
Lemma lem5414544 : term280 = term255.
Proof. exact (@lem996238 term255). Qed.
Lemma lem5414545 : (term280 = term255) = (term281 = term257).
Proof. exact (@lem1007663 (BIT1 0) term255 term255). Qed.
Lemma lem5414546 : term281 = term257.
Proof. exact (EQ_MP (@lem5414545) (@lem5414544)). Qed.
Lemma lem5414547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414548 : term282 = term243.
Proof. exact (MK_COMB (@lem5414547) (@lem5414546)). Qed.
Lemma lem5414549 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5414550 : term279 = term283.
Proof. exact (MK_COMB (@lem5414549) (@lem5414548)). Qed.
Lemma lem5414551 : term274 = term283.
Proof. exact (TRANS (@lem5414543) (@lem5414550)). Qed.
Lemma lem5414552 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5414553 : term284 = term285.
Proof. exact (MK_COMB (@lem5414552) (@lem5414551)). Qed.
Lemma lem5414554 : term276 = term286.
Proof. exact (MK_COMB (@lem5414553) (@lem5414540)). Qed.
Lemma lem5414555 : term275 = term286.
Proof. exact (TRANS (@lem5414532) (@lem5414554)). Qed.
Lemma lem5414556 : term274 = term286.
Proof. exact (TRANS (@lem5414531) (@lem5414555)). Qed.
Lemma lem5414558 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5414559 : term286 = term283.
Proof. exact (@lem5414558 term283). Qed.
Lemma lem5414560 : term274 = term283.
Proof. exact (TRANS (@lem5414556) (@lem5414559)). Qed.
Lemma lem5414563 (_69910 : int) : (term287 _69910) = (term287 _69910).
Proof. exact (eq_refl (term287 _69910)). Qed.
Lemma lem5414564 (_69910 : int) : (term273 _69910) = (term288 _69910).
Proof. exact (MK_COMB (@lem5414563 _69910) (@lem5414560)). Qed.
Lemma lem5414565 (_69910 : int) : (term272 _69910) = (term288 _69910).
Proof. exact (TRANS (@lem5414522 _69910) (@lem5414564 _69910)). Qed.
Lemma lem5414566 (_69911 : int) : (term171 _69911) = (term171 _69911).
Proof. exact (eq_refl (term171 _69911)). Qed.
Lemma lem5414567 (_69911 : int) (_69910 : int) : (term271 _69911 _69910) = (term289 _69911 _69910).
Proof. exact (MK_COMB (@lem5414566 _69911) (@lem5414565 _69910)). Qed.
Lemma lem5414572 (_69910 : int) (_69911 : int) : (term289 _69911 _69910) = (term309 _69910 _69911).
Proof. exact (@lem1982757 (term310 _69910) (real_of_int _69911) term283). Qed.
Lemma lem5414573 (_69910 : int) (_69911 : int) : (term271 _69911 _69910) = (term309 _69910 _69911).
Proof. exact (TRANS (@lem5414567 _69911 _69910) (@lem5414572 _69910 _69911)). Qed.
Lemma lem5414574 (_69910 : int) (_69911 : int) : (term270 _69911 _69910) = (term309 _69910 _69911).
Proof. exact (TRANS (@lem5414521 _69911 _69910) (@lem5414573 _69910 _69911)). Qed.
Lemma lem5414575 (_69910 : int) (_69911 : int) : (term269 _69911 _69910) = (term309 _69910 _69911).
Proof. exact (TRANS (@lem5414520 _69911 _69910) (@lem5414574 _69910 _69911)). Qed.
Lemma lem5414576 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414577 (_69910 : int) (_69911 : int) : (term290 _69911 _69910) = (term311 _69910 _69911).
Proof. exact (MK_COMB (@lem5414576) (@lem5414575 _69910 _69911)). Qed.
Lemma lem5414578 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414579 (_69910 : int) (_69911 : int) : (term235 _69911 _69910) = (term312 _69910 _69911).
Proof. exact (MK_COMB (@lem5414577 _69910 _69911) (@lem5414578)). Qed.
Lemma lem5414580 (_69910 : int) (_69911 : int) : (term178 _69910 _69911) = (term312 _69910 _69911).
Proof. exact (TRANS (@lem5414388 _69911 _69910) (@lem5414579 _69910 _69911)). Qed.
Lemma lem5414581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5414582 (_69909 : int) (_69911 : int) : (term184 _69911 _69909) = (term313 _69909 _69911).
Proof. exact (MK_COMB (@lem5414581) (@lem5414387 _69909 _69911)). Qed.
Lemma lem5414583 (_69909 : int) (_69910 : int) (_69911 : int) : (term185 _69909 _69910 _69911) = (term314 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414582 _69909 _69911) (@lem5414580 _69910 _69911)). Qed.
Lemma lem5414584 (_69911 : int) (_69909 : int) : (term148 _69909 _69911) = (term315 _69911 _69909).
Proof. exact (@lem1988287 (real_of_int _69911) (real_of_int _69909)). Qed.
Lemma lem5414590 (_69911 : int) (_69909 : int) : (term316 _69911 _69909) = (term317 _69911 _69909).
Proof. exact (@lem1982792 (real_of_int _69911) (real_of_int _69909)). Qed.
Lemma lem5414595 (_69909 : int) (_69911 : int) : (term317 _69911 _69909) = (term318 _69909 _69911).
Proof. exact (@lem1982761 (term310 _69909) (real_of_int _69911)). Qed.
Lemma lem5414597 (_69909 : int) (_69911 : int) : (term316 _69911 _69909) = (term318 _69909 _69911).
Proof. exact (TRANS (@lem5414590 _69911 _69909) (@lem5414595 _69909 _69911)). Qed.
Lemma lem5414598 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414599 (_69909 : int) (_69911 : int) : (term319 _69911 _69909) = (term320 _69909 _69911).
Proof. exact (MK_COMB (@lem5414598) (@lem5414597 _69909 _69911)). Qed.
Lemma lem5414600 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414601 (_69909 : int) (_69911 : int) : (term315 _69911 _69909) = (term321 _69909 _69911).
Proof. exact (MK_COMB (@lem5414599 _69909 _69911) (@lem5414600)). Qed.
Lemma lem5414602 (_69909 : int) (_69911 : int) : (term148 _69909 _69911) = (term321 _69909 _69911).
Proof. exact (TRANS (@lem5414584 _69911 _69909) (@lem5414601 _69909 _69911)). Qed.
Lemma lem5414603 (_69910 : int) (_69911 : int) : (term148 _69911 _69910) = (term315 _69910 _69911).
Proof. exact (@lem1988287 (real_of_int _69910) (real_of_int _69911)). Qed.
Lemma lem5414616 (_69910 : int) (_69911 : int) : (term316 _69910 _69911) = (term317 _69910 _69911).
Proof. exact (@lem1982792 (real_of_int _69910) (real_of_int _69911)). Qed.
Lemma lem5414617 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414618 (_69910 : int) (_69911 : int) : (term319 _69910 _69911) = (term322 _69910 _69911).
Proof. exact (MK_COMB (@lem5414617) (@lem5414616 _69910 _69911)). Qed.
Lemma lem5414619 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414620 (_69910 : int) (_69911 : int) : (term315 _69910 _69911) = (term323 _69910 _69911).
Proof. exact (MK_COMB (@lem5414618 _69910 _69911) (@lem5414619)). Qed.
Lemma lem5414621 (_69910 : int) (_69911 : int) : (term148 _69911 _69910) = (term323 _69910 _69911).
Proof. exact (TRANS (@lem5414603 _69910 _69911) (@lem5414620 _69910 _69911)). Qed.
Lemma lem5414622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5414623 (_69909 : int) (_69911 : int) : (term186 _69909 _69911) = (term324 _69909 _69911).
Proof. exact (MK_COMB (@lem5414622) (@lem5414602 _69909 _69911)). Qed.
Lemma lem5414624 (_69909 : int) (_69910 : int) (_69911 : int) : (term187 _69909 _69911 _69910) = (term325 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414623 _69909 _69911) (@lem5414621 _69910 _69911)). Qed.
Lemma lem5414625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5414626 (_69909 : int) (_69910 : int) (_69911 : int) : (term188 _69909 _69910 _69911) = (term326 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414625) (@lem5414583 _69909 _69910 _69911)). Qed.
Lemma lem5414627 (_69909 : int) (_69910 : int) (_69911 : int) : (term189 _69909 _69911 _69910) = (term327 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414626 _69909 _69910 _69911) (@lem5414624 _69909 _69910 _69911)). Qed.
Lemma lem5414628 (_69911 : int) (_69909 : int) : (term148 _69909 _69911) = (term315 _69911 _69909).
Proof. exact (@lem1988287 (real_of_int _69911) (real_of_int _69909)). Qed.
Lemma lem5414634 (_69911 : int) (_69909 : int) : (term316 _69911 _69909) = (term317 _69911 _69909).
Proof. exact (@lem1982792 (real_of_int _69911) (real_of_int _69909)). Qed.
Lemma lem5414639 (_69909 : int) (_69911 : int) : (term317 _69911 _69909) = (term318 _69909 _69911).
Proof. exact (@lem1982761 (term310 _69909) (real_of_int _69911)). Qed.
Lemma lem5414641 (_69909 : int) (_69911 : int) : (term316 _69911 _69909) = (term318 _69909 _69911).
Proof. exact (TRANS (@lem5414634 _69911 _69909) (@lem5414639 _69909 _69911)). Qed.
Lemma lem5414642 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414643 (_69909 : int) (_69911 : int) : (term319 _69911 _69909) = (term320 _69909 _69911).
Proof. exact (MK_COMB (@lem5414642) (@lem5414641 _69909 _69911)). Qed.
Lemma lem5414644 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414645 (_69909 : int) (_69911 : int) : (term315 _69911 _69909) = (term321 _69909 _69911).
Proof. exact (MK_COMB (@lem5414643 _69909 _69911) (@lem5414644)). Qed.
Lemma lem5414646 (_69909 : int) (_69911 : int) : (term148 _69909 _69911) = (term321 _69909 _69911).
Proof. exact (TRANS (@lem5414628 _69911 _69909) (@lem5414645 _69909 _69911)). Qed.
Lemma lem5414647 (_69910 : int) (_69911 : int) : (term192 _69911 _69910) = (term328 _69910 _69911).
Proof. exact (@lem1988287 (term172 _69910) (real_of_int _69911)). Qed.
Lemma lem5414659 (_69910 : int) (_69911 : int) : (term329 _69910 _69911) = (term330 _69910 _69911).
Proof. exact (@lem1982792 (term172 _69910) (real_of_int _69911)). Qed.
Lemma lem5414663 (_69910 : int) (_69911 : int) : (term330 _69910 _69911) = (term331 _69910 _69911).
Proof. exact (@lem1982755 (real_of_int _69910) term170 (term310 _69911)). Qed.
Lemma lem5414664 (_69911 : int) : (term332 _69911) = (term333 _69911).
Proof. exact (@lem1982761 (term310 _69911) term170). Qed.
Lemma lem5414665 (_69910 : int) : (term171 _69910) = (term171 _69910).
Proof. exact (eq_refl (term171 _69910)). Qed.
Lemma lem5414666 (_69910 : int) (_69911 : int) : (term331 _69910 _69911) = (term334 _69910 _69911).
Proof. exact (MK_COMB (@lem5414665 _69910) (@lem5414664 _69911)). Qed.
Lemma lem5414668 (_69910 : int) (_69911 : int) : (term330 _69910 _69911) = (term334 _69910 _69911).
Proof. exact (TRANS (@lem5414663 _69910 _69911) (@lem5414666 _69910 _69911)). Qed.
Lemma lem5414670 (_69910 : int) (_69911 : int) : (term329 _69910 _69911) = (term334 _69910 _69911).
Proof. exact (TRANS (@lem5414659 _69910 _69911) (@lem5414668 _69910 _69911)). Qed.
Lemma lem5414671 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414672 (_69910 : int) (_69911 : int) : (term335 _69910 _69911) = (term336 _69910 _69911).
Proof. exact (MK_COMB (@lem5414671) (@lem5414670 _69910 _69911)). Qed.
Lemma lem5414673 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414674 (_69910 : int) (_69911 : int) : (term328 _69910 _69911) = (term337 _69910 _69911).
Proof. exact (MK_COMB (@lem5414672 _69910 _69911) (@lem5414673)). Qed.
Lemma lem5414675 (_69910 : int) (_69911 : int) : (term192 _69911 _69910) = (term337 _69910 _69911).
Proof. exact (TRANS (@lem5414647 _69910 _69911) (@lem5414674 _69910 _69911)). Qed.
Lemma lem5414676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5414677 (_69909 : int) (_69911 : int) : (term186 _69909 _69911) = (term324 _69909 _69911).
Proof. exact (MK_COMB (@lem5414676) (@lem5414646 _69909 _69911)). Qed.
Lemma lem5414678 (_69909 : int) (_69910 : int) (_69911 : int) : (term193 _69909 _69911 _69910) = (term338 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414677 _69909 _69911) (@lem5414675 _69910 _69911)). Qed.
Lemma lem5414679 (_69909 : int) (_69911 : int) : (term182 _69911 _69909) = (term293 _69909 _69911).
Proof. exact (@lem1988287 (real_of_int _69909) (term172 _69911)). Qed.
Lemma lem5414691 (_69909 : int) (_69911 : int) : (term294 _69909 _69911) = (term295 _69909 _69911).
Proof. exact (@lem1982792 (real_of_int _69909) (term172 _69911)). Qed.
Lemma lem5414692 (_69911 : int) : (term296 _69911) = (term297 _69911).
Proof. exact (@lem1982781 (real_of_int _69911) term214 term170). Qed.
Lemma lem5414694 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414695 : term170 = term237.
Proof. exact (@lem5414694 term69). Qed.
Lemma lem5414697 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5414698 : term214 = term215.
Proof. exact (@lem5414697 term69). Qed.
Lemma lem5414699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414700 : term216 = term217.
Proof. exact (MK_COMB (@lem5414699) (@lem5414698)). Qed.
Lemma lem5414701 : term298 = term299.
Proof. exact (MK_COMB (@lem5414700) (@lem5414695)). Qed.
Lemma lem5414702 : term299 = term300.
Proof. exact (@lem1981613 term214 term170 term170 term170). Qed.
Lemma lem5414704 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414705 : term223 = term224.
Proof. exact (@lem5414704 term69 term69). Qed.
Lemma lem5414706 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414707 : term226 = term69.
Proof. exact (EQ_MP (@lem5414706) (@lem940073)). Qed.
Lemma lem5414708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414709 : term224 = term170.
Proof. exact (MK_COMB (@lem5414708) (@lem5414707)). Qed.
Lemma lem5414710 : term223 = term170.
Proof. exact (TRANS (@lem5414705) (@lem5414709)). Qed.
Lemma lem5414712 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5414713 : term298 = term301.
Proof. exact (@lem5414712 term69 term69). Qed.
Lemma lem5414714 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414715 : term226 = term69.
Proof. exact (EQ_MP (@lem5414714) (@lem940073)). Qed.
Lemma lem5414716 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414717 : term224 = term170.
Proof. exact (MK_COMB (@lem5414716) (@lem5414715)). Qed.
Lemma lem5414718 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5414719 : term301 = term214.
Proof. exact (MK_COMB (@lem5414718) (@lem5414717)). Qed.
Lemma lem5414720 : term298 = term214.
Proof. exact (TRANS (@lem5414713) (@lem5414719)). Qed.
Lemma lem5414721 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5414722 : term302 = term303.
Proof. exact (MK_COMB (@lem5414721) (@lem5414720)). Qed.
Lemma lem5414723 : term300 = term215.
Proof. exact (MK_COMB (@lem5414722) (@lem5414710)). Qed.
Lemma lem5414724 : term299 = term215.
Proof. exact (TRANS (@lem5414702) (@lem5414723)). Qed.
Lemma lem5414725 : term298 = term215.
Proof. exact (TRANS (@lem5414701) (@lem5414724)). Qed.
Lemma lem5414727 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5414728 : term215 = term214.
Proof. exact (@lem5414727 term214). Qed.
Lemma lem5414729 : term298 = term214.
Proof. exact (TRANS (@lem5414725) (@lem5414728)). Qed.
Lemma lem5414732 (_69911 : int) : (term287 _69911) = (term287 _69911).
Proof. exact (eq_refl (term287 _69911)). Qed.
Lemma lem5414733 (_69911 : int) : (term297 _69911) = (term304 _69911).
Proof. exact (MK_COMB (@lem5414732 _69911) (@lem5414729)). Qed.
Lemma lem5414734 (_69911 : int) : (term296 _69911) = (term304 _69911).
Proof. exact (TRANS (@lem5414692 _69911) (@lem5414733 _69911)). Qed.
Lemma lem5414735 (_69909 : int) : (term171 _69909) = (term171 _69909).
Proof. exact (eq_refl (term171 _69909)). Qed.
Lemma lem5414738 (_69909 : int) (_69911 : int) : (term295 _69909 _69911) = (term305 _69909 _69911).
Proof. exact (MK_COMB (@lem5414735 _69909) (@lem5414734 _69911)). Qed.
Lemma lem5414740 (_69909 : int) (_69911 : int) : (term294 _69909 _69911) = (term305 _69909 _69911).
Proof. exact (TRANS (@lem5414691 _69909 _69911) (@lem5414738 _69909 _69911)). Qed.
Lemma lem5414741 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414742 (_69909 : int) (_69911 : int) : (term306 _69909 _69911) = (term307 _69909 _69911).
Proof. exact (MK_COMB (@lem5414741) (@lem5414740 _69909 _69911)). Qed.
Lemma lem5414743 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414744 (_69909 : int) (_69911 : int) : (term293 _69909 _69911) = (term308 _69909 _69911).
Proof. exact (MK_COMB (@lem5414742 _69909 _69911) (@lem5414743)). Qed.
Lemma lem5414745 (_69909 : int) (_69911 : int) : (term182 _69911 _69909) = (term308 _69909 _69911).
Proof. exact (TRANS (@lem5414679 _69909 _69911) (@lem5414744 _69909 _69911)). Qed.
Lemma lem5414746 (_69911 : int) (_69910 : int) : (term182 _69910 _69911) = (term293 _69911 _69910).
Proof. exact (@lem1988287 (real_of_int _69911) (term172 _69910)). Qed.
Lemma lem5414758 (_69911 : int) (_69910 : int) : (term294 _69911 _69910) = (term295 _69911 _69910).
Proof. exact (@lem1982792 (real_of_int _69911) (term172 _69910)). Qed.
Lemma lem5414759 (_69910 : int) : (term296 _69910) = (term297 _69910).
Proof. exact (@lem1982781 (real_of_int _69910) term214 term170). Qed.
Lemma lem5414761 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5414762 : term170 = term237.
Proof. exact (@lem5414761 term69). Qed.
Lemma lem5414764 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5414765 : term214 = term215.
Proof. exact (@lem5414764 term69). Qed.
Lemma lem5414766 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5414767 : term216 = term217.
Proof. exact (MK_COMB (@lem5414766) (@lem5414765)). Qed.
Lemma lem5414768 : term298 = term299.
Proof. exact (MK_COMB (@lem5414767) (@lem5414762)). Qed.
Lemma lem5414769 : term299 = term300.
Proof. exact (@lem1981613 term214 term170 term170 term170). Qed.
Lemma lem5414771 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5414772 : term223 = term224.
Proof. exact (@lem5414771 term69 term69). Qed.
Lemma lem5414773 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414774 : term226 = term69.
Proof. exact (EQ_MP (@lem5414773) (@lem940073)). Qed.
Lemma lem5414775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414776 : term224 = term170.
Proof. exact (MK_COMB (@lem5414775) (@lem5414774)). Qed.
Lemma lem5414777 : term223 = term170.
Proof. exact (TRANS (@lem5414772) (@lem5414776)). Qed.
Lemma lem5414779 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5414780 : term298 = term301.
Proof. exact (@lem5414779 term69 term69). Qed.
Lemma lem5414781 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5414782 : term226 = term69.
Proof. exact (EQ_MP (@lem5414781) (@lem940073)). Qed.
Lemma lem5414783 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5414784 : term224 = term170.
Proof. exact (MK_COMB (@lem5414783) (@lem5414782)). Qed.
Lemma lem5414785 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5414786 : term301 = term214.
Proof. exact (MK_COMB (@lem5414785) (@lem5414784)). Qed.
Lemma lem5414787 : term298 = term214.
Proof. exact (TRANS (@lem5414780) (@lem5414786)). Qed.
Lemma lem5414788 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5414789 : term302 = term303.
Proof. exact (MK_COMB (@lem5414788) (@lem5414787)). Qed.
Lemma lem5414790 : term300 = term215.
Proof. exact (MK_COMB (@lem5414789) (@lem5414777)). Qed.
Lemma lem5414791 : term299 = term215.
Proof. exact (TRANS (@lem5414769) (@lem5414790)). Qed.
Lemma lem5414792 : term298 = term215.
Proof. exact (TRANS (@lem5414768) (@lem5414791)). Qed.
Lemma lem5414794 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5414795 : term215 = term214.
Proof. exact (@lem5414794 term214). Qed.
Lemma lem5414796 : term298 = term214.
Proof. exact (TRANS (@lem5414792) (@lem5414795)). Qed.
Lemma lem5414799 (_69910 : int) : (term287 _69910) = (term287 _69910).
Proof. exact (eq_refl (term287 _69910)). Qed.
Lemma lem5414800 (_69910 : int) : (term297 _69910) = (term304 _69910).
Proof. exact (MK_COMB (@lem5414799 _69910) (@lem5414796)). Qed.
Lemma lem5414801 (_69910 : int) : (term296 _69910) = (term304 _69910).
Proof. exact (TRANS (@lem5414759 _69910) (@lem5414800 _69910)). Qed.
Lemma lem5414802 (_69911 : int) : (term171 _69911) = (term171 _69911).
Proof. exact (eq_refl (term171 _69911)). Qed.
Lemma lem5414803 (_69911 : int) (_69910 : int) : (term295 _69911 _69910) = (term305 _69911 _69910).
Proof. exact (MK_COMB (@lem5414802 _69911) (@lem5414801 _69910)). Qed.
Lemma lem5414808 (_69910 : int) (_69911 : int) : (term305 _69911 _69910) = (term339 _69910 _69911).
Proof. exact (@lem1982757 (term310 _69910) (real_of_int _69911) term214). Qed.
Lemma lem5414809 (_69910 : int) (_69911 : int) : (term295 _69911 _69910) = (term339 _69910 _69911).
Proof. exact (TRANS (@lem5414803 _69911 _69910) (@lem5414808 _69910 _69911)). Qed.
Lemma lem5414811 (_69910 : int) (_69911 : int) : (term294 _69911 _69910) = (term339 _69910 _69911).
Proof. exact (TRANS (@lem5414758 _69911 _69910) (@lem5414809 _69910 _69911)). Qed.
Lemma lem5414812 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5414813 (_69910 : int) (_69911 : int) : (term306 _69911 _69910) = (term340 _69910 _69911).
Proof. exact (MK_COMB (@lem5414812) (@lem5414811 _69910 _69911)). Qed.
Lemma lem5414814 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5414815 (_69910 : int) (_69911 : int) : (term293 _69911 _69910) = (term341 _69910 _69911).
Proof. exact (MK_COMB (@lem5414813 _69910 _69911) (@lem5414814)). Qed.
Lemma lem5414816 (_69910 : int) (_69911 : int) : (term182 _69910 _69911) = (term341 _69910 _69911).
Proof. exact (TRANS (@lem5414746 _69911 _69910) (@lem5414815 _69910 _69911)). Qed.
Lemma lem5414817 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5414818 (_69909 : int) (_69911 : int) : (term184 _69911 _69909) = (term313 _69909 _69911).
Proof. exact (MK_COMB (@lem5414817) (@lem5414745 _69909 _69911)). Qed.
Lemma lem5414819 (_69909 : int) (_69910 : int) (_69911 : int) : (term194 _69909 _69910 _69911) = (term342 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414818 _69909 _69911) (@lem5414816 _69910 _69911)). Qed.
Lemma lem5414820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5414821 (_69909 : int) (_69910 : int) (_69911 : int) : (term195 _69909 _69911 _69910) = (term343 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414820) (@lem5414678 _69909 _69910 _69911)). Qed.
Lemma lem5414822 (_69909 : int) (_69910 : int) (_69911 : int) : (term196 _69909 _69910 _69911) = (term344 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414821 _69909 _69910 _69911) (@lem5414819 _69909 _69910 _69911)). Qed.
Lemma lem5414823 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5414824 (_69909 : int) (_69910 : int) (_69911 : int) : (term197 _69909 _69911 _69910) = (term345 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414823) (@lem5414627 _69909 _69910 _69911)). Qed.
Lemma lem5414825 (_69909 : int) (_69910 : int) (_69911 : int) : (term198 _69909 _69910 _69911) = (term346 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414824 _69909 _69910 _69911) (@lem5414822 _69909 _69910 _69911)). Qed.
Lemma lem5414826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5414827 (_69909 : int) (_69910 : int) : (term199 _69910 _69909) = (term347 _69909 _69910).
Proof. exact (MK_COMB (@lem5414826) (@lem5414320 _69909 _69910)). Qed.
Lemma lem5414828 (_69909 : int) (_69910 : int) (_69911 : int) : (term200 _69909 _69910 _69911) = (term348 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414827 _69909 _69910) (@lem5414825 _69909 _69910 _69911)). Qed.
Lemma lem5414829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5414830 (_69911 : int) : (term201 _69911) = (term349 _69911).
Proof. exact (MK_COMB (@lem5414829) (@lem5414131 _69911)). Qed.
Lemma lem5414831 (_69909 : int) (_69910 : int) (_69911 : int) : (term202 _69909 _69910 _69911) = (term350 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414830 _69911) (@lem5414828 _69909 _69910 _69911)). Qed.
Lemma lem5414832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5414833 (_69910 : int) : (term201 _69910) = (term349 _69910).
Proof. exact (MK_COMB (@lem5414832) (@lem5414083 _69910)). Qed.
Lemma lem5414834 (_69909 : int) (_69910 : int) (_69911 : int) : (term203 _69909 _69910 _69911) = (term351 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414833 _69910) (@lem5414831 _69909 _69910 _69911)). Qed.
Lemma lem5414835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5414836 (_69909 : int) : (term201 _69909) = (term349 _69909).
Proof. exact (MK_COMB (@lem5414835) (@lem5414035 _69909)). Qed.
Lemma lem5414837 (_69909 : int) (_69910 : int) (_69911 : int) : (term204 _69909 _69910 _69911) = (term352 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414836 _69909) (@lem5414834 _69909 _69910 _69911)). Qed.
Lemma lem5414844 (_69909 : int) (_69910 : int) (_69911 : int) : (term206 _69909 _69910 _69911) = (term352 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5413987 _69909 _69910 _69911) (@lem5414837 _69909 _69910 _69911)). Qed.
Lemma lem5414867 (_69909 : int) (_69910 : int) (_69911 : int) : (term344 _69909 _69910 _69911) = (term353 _69909 _69910 _69911).
Proof. exact (@lem19158 (term308 _69909 _69911) (term338 _69909 _69910 _69911) (term341 _69910 _69911)). Qed.
Lemma lem5414890 (_69909 : int) (_69910 : int) (_69911 : int) : (term327 _69909 _69910 _69911) = (term354 _69909 _69910 _69911).
Proof. exact (@lem19367 (term308 _69909 _69911) (term312 _69910 _69911) (term325 _69909 _69910 _69911)). Qed.
Lemma lem5414891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5414892 (_69909 : int) (_69910 : int) (_69911 : int) : (term345 _69909 _69910 _69911) = (term355 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414891) (@lem5414890 _69909 _69910 _69911)). Qed.
Lemma lem5414893 (_69909 : int) (_69910 : int) (_69911 : int) : (term346 _69909 _69910 _69911) = (term356 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414892 _69909 _69910 _69911) (@lem5414867 _69909 _69910 _69911)). Qed.
Lemma lem5414896 (_69909 : int) (_69910 : int) : (term347 _69909 _69910) = (term347 _69909 _69910).
Proof. exact (eq_refl (term347 _69909 _69910)). Qed.
Lemma lem5414897 (_69909 : int) (_69910 : int) (_69911 : int) : (term348 _69909 _69910 _69911) = (term357 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414896 _69909 _69910) (@lem5414893 _69909 _69910 _69911)). Qed.
Lemma lem5414898 (_69909 : int) (_69910 : int) (_69911 : int) : (term357 _69909 _69910 _69911) = (term358 _69909 _69910 _69911).
Proof. exact (@lem19158 (term354 _69909 _69910 _69911) (term292 _69909 _69910) (term353 _69909 _69910 _69911)). Qed.
Lemma lem5414905 (_69909 : int) (_69910 : int) (_69911 : int) : (term359 _69909 _69910 _69911) = (term360 _69909 _69910 _69911).
Proof. exact (@lem19158 (term361 _69910 _69909 _69911) (term292 _69909 _69910) (term362 _69909 _69910 _69911)). Qed.
Lemma lem5414912 (_69909 : int) (_69910 : int) (_69911 : int) : (term363 _69909 _69910 _69911) = (term364 _69909 _69910 _69911).
Proof. exact (@lem19158 (term365 _69909 _69910 _69911) (term292 _69909 _69910) (term366 _69909 _69910 _69911)). Qed.
Lemma lem5414913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5414914 (_69909 : int) (_69910 : int) (_69911 : int) : (term367 _69909 _69910 _69911) = (term368 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414913) (@lem5414912 _69909 _69910 _69911)). Qed.
Lemma lem5414915 (_69909 : int) (_69910 : int) (_69911 : int) : (term358 _69909 _69910 _69911) = (term369 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414914 _69909 _69910 _69911) (@lem5414905 _69909 _69910 _69911)). Qed.
Lemma lem5414916 (_69909 : int) (_69910 : int) (_69911 : int) : (term357 _69909 _69910 _69911) = (term369 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414898 _69909 _69910 _69911) (@lem5414915 _69909 _69910 _69911)). Qed.
Lemma lem5414917 (_69909 : int) (_69910 : int) (_69911 : int) : (term348 _69909 _69910 _69911) = (term369 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414897 _69909 _69910 _69911) (@lem5414916 _69909 _69910 _69911)). Qed.
Lemma lem5414920 (_69911 : int) : (term349 _69911) = (term349 _69911).
Proof. exact (eq_refl (term349 _69911)). Qed.
Lemma lem5414921 (_69909 : int) (_69910 : int) (_69911 : int) : (term350 _69909 _69910 _69911) = (term370 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414920 _69911) (@lem5414917 _69909 _69910 _69911)). Qed.
Lemma lem5414922 (_69909 : int) (_69910 : int) (_69911 : int) : (term370 _69909 _69910 _69911) = (term371 _69909 _69910 _69911).
Proof. exact (@lem19158 (term364 _69909 _69910 _69911) (term234 _69911) (term360 _69909 _69910 _69911)). Qed.
Lemma lem5414929 (_69909 : int) (_69910 : int) (_69911 : int) : (term372 _69909 _69910 _69911) = (term373 _69909 _69910 _69911).
Proof. exact (@lem19158 (term374 _69910 _69909 _69911) (term234 _69911) (term375 _69909 _69910 _69911)). Qed.
Lemma lem5414936 (_69909 : int) (_69910 : int) (_69911 : int) : (term376 _69909 _69910 _69911) = (term377 _69909 _69910 _69911).
Proof. exact (@lem19158 (term378 _69909 _69910 _69911) (term234 _69911) (term379 _69909 _69910 _69911)). Qed.
Lemma lem5414937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5414938 (_69909 : int) (_69910 : int) (_69911 : int) : (term380 _69909 _69910 _69911) = (term381 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414937) (@lem5414936 _69909 _69910 _69911)). Qed.
Lemma lem5414939 (_69909 : int) (_69910 : int) (_69911 : int) : (term371 _69909 _69910 _69911) = (term382 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414938 _69909 _69910 _69911) (@lem5414929 _69909 _69910 _69911)). Qed.
Lemma lem5414940 (_69909 : int) (_69910 : int) (_69911 : int) : (term370 _69909 _69910 _69911) = (term382 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414922 _69909 _69910 _69911) (@lem5414939 _69909 _69910 _69911)). Qed.
Lemma lem5414941 (_69909 : int) (_69910 : int) (_69911 : int) : (term350 _69909 _69910 _69911) = (term382 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414921 _69909 _69910 _69911) (@lem5414940 _69909 _69910 _69911)). Qed.
Lemma lem5414944 (_69910 : int) : (term349 _69910) = (term349 _69910).
Proof. exact (eq_refl (term349 _69910)). Qed.
Lemma lem5414945 (_69909 : int) (_69910 : int) (_69911 : int) : (term351 _69909 _69910 _69911) = (term383 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414944 _69910) (@lem5414941 _69909 _69910 _69911)). Qed.
Lemma lem5414946 (_69909 : int) (_69910 : int) (_69911 : int) : (term383 _69909 _69910 _69911) = (term384 _69909 _69910 _69911).
Proof. exact (@lem19158 (term377 _69909 _69910 _69911) (term234 _69910) (term373 _69909 _69910 _69911)). Qed.
Lemma lem5414953 (_69909 : int) (_69910 : int) (_69911 : int) : (term385 _69909 _69910 _69911) = (term386 _69909 _69910 _69911).
Proof. exact (@lem19158 (term387 _69910 _69909 _69911) (term234 _69910) (term388 _69909 _69910 _69911)). Qed.
Lemma lem5414960 (_69909 : int) (_69910 : int) (_69911 : int) : (term389 _69909 _69910 _69911) = (term390 _69909 _69910 _69911).
Proof. exact (@lem19158 (term391 _69909 _69910 _69911) (term234 _69910) (term392 _69909 _69910 _69911)). Qed.
Lemma lem5414961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5414962 (_69909 : int) (_69910 : int) (_69911 : int) : (term393 _69909 _69910 _69911) = (term394 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414961) (@lem5414960 _69909 _69910 _69911)). Qed.
Lemma lem5414963 (_69909 : int) (_69910 : int) (_69911 : int) : (term384 _69909 _69910 _69911) = (term395 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414962 _69909 _69910 _69911) (@lem5414953 _69909 _69910 _69911)). Qed.
Lemma lem5414964 (_69909 : int) (_69910 : int) (_69911 : int) : (term383 _69909 _69910 _69911) = (term395 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414946 _69909 _69910 _69911) (@lem5414963 _69909 _69910 _69911)). Qed.
Lemma lem5414965 (_69909 : int) (_69910 : int) (_69911 : int) : (term351 _69909 _69910 _69911) = (term395 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414945 _69909 _69910 _69911) (@lem5414964 _69909 _69910 _69911)). Qed.
Lemma lem5414968 (_69909 : int) : (term349 _69909) = (term349 _69909).
Proof. exact (eq_refl (term349 _69909)). Qed.
Lemma lem5414969 (_69909 : int) (_69910 : int) (_69911 : int) : (term352 _69909 _69910 _69911) = (term396 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414968 _69909) (@lem5414965 _69909 _69910 _69911)). Qed.
Lemma lem5414970 (_69909 : int) (_69910 : int) (_69911 : int) : (term396 _69909 _69910 _69911) = (term397 _69909 _69910 _69911).
Proof. exact (@lem19158 (term390 _69909 _69910 _69911) (term234 _69909) (term386 _69909 _69910 _69911)). Qed.
Lemma lem5414977 (_69909 : int) (_69910 : int) (_69911 : int) : (term398 _69909 _69910 _69911) = (term399 _69909 _69910 _69911).
Proof. exact (@lem19158 (term400 _69910 _69909 _69911) (term234 _69909) (term401 _69909 _69910 _69911)). Qed.
Lemma lem5414984 (_69909 : int) (_69910 : int) (_69911 : int) : (term402 _69909 _69910 _69911) = (term403 _69909 _69910 _69911).
Proof. exact (@lem19158 (term404 _69909 _69910 _69911) (term234 _69909) (term405 _69909 _69910 _69911)). Qed.
Lemma lem5414985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5414986 (_69909 : int) (_69910 : int) (_69911 : int) : (term406 _69909 _69910 _69911) = (term407 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414985) (@lem5414984 _69909 _69910 _69911)). Qed.
Lemma lem5414987 (_69909 : int) (_69910 : int) (_69911 : int) : (term397 _69909 _69910 _69911) = (term408 _69909 _69910 _69911).
Proof. exact (MK_COMB (@lem5414986 _69909 _69910 _69911) (@lem5414977 _69909 _69910 _69911)). Qed.
Lemma lem5414988 (_69909 : int) (_69910 : int) (_69911 : int) : (term396 _69909 _69910 _69911) = (term408 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414970 _69909 _69910 _69911) (@lem5414987 _69909 _69910 _69911)). Qed.
Lemma lem5414989 (_69909 : int) (_69910 : int) (_69911 : int) : (term352 _69909 _69910 _69911) = (term408 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414969 _69909 _69910 _69911) (@lem5414988 _69909 _69910 _69911)). Qed.
Lemma lem5414990 (_69909 : int) (_69910 : int) (_69911 : int) : (term206 _69909 _69910 _69911) = (term408 _69909 _69910 _69911).
Proof. exact (TRANS (@lem5414844 _69909 _69910 _69911) (@lem5414989 _69909 _69910 _69911)). Qed.
Lemma lem5415012 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term408 _69909 _69910 _69911) : term408 _69909 _69910 _69911.
Proof. exact (h1). Qed.
Lemma lem5415013 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term403 _69909 _69910 _69911) : term403 _69909 _69910 _69911.
Proof. exact (h1). Qed.
Lemma lem5415014 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term409 _69909 _69910 _69911.
Proof. exact (h1). Qed.
Lemma lem5415015 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term404 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415014 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415017 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term391 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415015 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415019 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term378 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415017 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415021 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term365 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415019 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415022 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term292 _69909 _69910.
Proof. exact (proj1 (@lem5415019 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415023 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term325 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415021 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415025 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term323 _69910 _69911.
Proof. exact (proj2 (@lem5415023 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415026 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term321 _69909 _69911.
Proof. exact (proj1 (@lem5415023 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415028 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5415029 : term410 = term245.
Proof. exact (@lem5415028 term153 term170). Qed.
Lemma lem5415031 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415032 : term170 = term237.
Proof. exact (@lem5415031 term69). Qed.
Lemma lem5415034 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415035 : term153 = term211.
Proof. exact (@lem5415034 (NUMERAL 0)). Qed.
Lemma lem5415036 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415037 : term411 = term412.
Proof. exact (MK_COMB (@lem5415036) (@lem5415035)). Qed.
Lemma lem5415038 : term245 = term413.
Proof. exact (MK_COMB (@lem5415037) (@lem5415032)). Qed.
Lemma lem5415039 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5415041 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415042 : term245 = term246.
Proof. exact (@lem5415041 (NUMERAL 0) term69). Qed.
Lemma lem5415043 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415044 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415045 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415044 h1) (fun h1 : term246 = True => @lem5415043)). Qed.
Lemma lem5415046 : term246 = True.
Proof. exact (EQ_MP (@lem5415045) (@lem5415043)). Qed.
Lemma lem5415047 : term245 = True.
Proof. exact (TRANS (@lem5415042) (@lem5415046)). Qed.
Lemma lem5415048 : True = term245.
Proof. exact (SYM (@lem5415047)). Qed.
Lemma lem5415049 : term245.
Proof. exact (EQ_MP (@lem5415048) (@lem0)). Qed.
Lemma lem5415050 : term415.
Proof. exact (@lem5415039 (@lem5415049)). Qed.
Lemma lem5415052 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415053 : term245 = term246.
Proof. exact (@lem5415052 (NUMERAL 0) term69). Qed.
Lemma lem5415054 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415055 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415056 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415055 h1) (fun h1 : term246 = True => @lem5415054)). Qed.
Lemma lem5415057 : term246 = True.
Proof. exact (EQ_MP (@lem5415056) (@lem5415054)). Qed.
Lemma lem5415058 : term245 = True.
Proof. exact (TRANS (@lem5415053) (@lem5415057)). Qed.
Lemma lem5415059 : True = term245.
Proof. exact (SYM (@lem5415058)). Qed.
Lemma lem5415060 : term245.
Proof. exact (EQ_MP (@lem5415059) (@lem0)). Qed.
Lemma lem5415061 : term413 = term416.
Proof. exact (@lem5415050 (@lem5415060)). Qed.
Lemma lem5415063 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415064 : term223 = term224.
Proof. exact (@lem5415063 term69 term69). Qed.
Lemma lem5415065 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415066 : term226 = term69.
Proof. exact (EQ_MP (@lem5415065) (@lem940073)). Qed.
Lemma lem5415067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415068 : term224 = term170.
Proof. exact (MK_COMB (@lem5415067) (@lem5415066)). Qed.
Lemma lem5415069 : term223 = term170.
Proof. exact (TRANS (@lem5415064) (@lem5415068)). Qed.
Lemma lem5415071 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415072 : term418 = term153.
Proof. exact (@lem5415071 term69). Qed.
Lemma lem5415073 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415074 : term419 = term411.
Proof. exact (MK_COMB (@lem5415073) (@lem5415072)). Qed.
Lemma lem5415075 : term416 = term245.
Proof. exact (MK_COMB (@lem5415074) (@lem5415069)). Qed.
Lemma lem5415077 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415078 : term245 = term246.
Proof. exact (@lem5415077 (NUMERAL 0) term69). Qed.
Lemma lem5415079 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415080 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415081 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415080 h1) (fun h1 : term246 = True => @lem5415079)). Qed.
Lemma lem5415082 : term246 = True.
Proof. exact (EQ_MP (@lem5415081) (@lem5415079)). Qed.
Lemma lem5415083 : term245 = True.
Proof. exact (TRANS (@lem5415078) (@lem5415082)). Qed.
Lemma lem5415084 : term416 = True.
Proof. exact (TRANS (@lem5415075) (@lem5415083)). Qed.
Lemma lem5415085 : term413 = True.
Proof. exact (TRANS (@lem5415061) (@lem5415084)). Qed.
Lemma lem5415086 : term245 = True.
Proof. exact (TRANS (@lem5415038) (@lem5415085)). Qed.
Lemma lem5415087 : term410 = True.
Proof. exact (TRANS (@lem5415029) (@lem5415086)). Qed.
Lemma lem5415088 : True = term410.
Proof. exact (SYM (@lem5415087)). Qed.
Lemma lem5415089 : term410.
Proof. exact (EQ_MP (@lem5415088) (@lem0)). Qed.
Lemma lem5415090 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term420 _69910 _69911.
Proof. exact (conj (@lem5415089) (@lem5415025 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415092 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5415093 (_69910 : int) (_69911 : int) : term422 _69910 _69911.
Proof. exact (@lem5415092 term170 (term317 _69910 _69911)). Qed.
Lemma lem5415094 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term423 _69910 _69911.
Proof. exact (@lem5415093 _69910 _69911 (@lem5415090 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415095 (_69910 : int) (_69911 : int) : (term424 _69910 _69911) = (term317 _69910 _69911).
Proof. exact (@lem1982733 (term317 _69910 _69911)). Qed.
Lemma lem5415096 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415097 (_69910 : int) (_69911 : int) : (term425 _69910 _69911) = (term322 _69910 _69911).
Proof. exact (MK_COMB (@lem5415096) (@lem5415095 _69910 _69911)). Qed.
Lemma lem5415098 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415099 (_69910 : int) (_69911 : int) : (term423 _69910 _69911) = (term323 _69910 _69911).
Proof. exact (MK_COMB (@lem5415097 _69910 _69911) (@lem5415098)). Qed.
Lemma lem5415100 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term323 _69910 _69911.
Proof. exact (EQ_MP (@lem5415099 _69910 _69911) (@lem5415094 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415102 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5415103 : term410 = term245.
Proof. exact (@lem5415102 term153 term170). Qed.
Lemma lem5415105 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415106 : term170 = term237.
Proof. exact (@lem5415105 term69). Qed.
Lemma lem5415108 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415109 : term153 = term211.
Proof. exact (@lem5415108 (NUMERAL 0)). Qed.
Lemma lem5415110 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415111 : term411 = term412.
Proof. exact (MK_COMB (@lem5415110) (@lem5415109)). Qed.
Lemma lem5415112 : term245 = term413.
Proof. exact (MK_COMB (@lem5415111) (@lem5415106)). Qed.
Lemma lem5415113 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5415115 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415116 : term245 = term246.
Proof. exact (@lem5415115 (NUMERAL 0) term69). Qed.
Lemma lem5415117 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415118 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415119 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415118 h1) (fun h1 : term246 = True => @lem5415117)). Qed.
Lemma lem5415120 : term246 = True.
Proof. exact (EQ_MP (@lem5415119) (@lem5415117)). Qed.
Lemma lem5415121 : term245 = True.
Proof. exact (TRANS (@lem5415116) (@lem5415120)). Qed.
Lemma lem5415122 : True = term245.
Proof. exact (SYM (@lem5415121)). Qed.
Lemma lem5415123 : term245.
Proof. exact (EQ_MP (@lem5415122) (@lem0)). Qed.
Lemma lem5415124 : term415.
Proof. exact (@lem5415113 (@lem5415123)). Qed.
Lemma lem5415126 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415127 : term245 = term246.
Proof. exact (@lem5415126 (NUMERAL 0) term69). Qed.
Lemma lem5415128 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415129 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415130 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415129 h1) (fun h1 : term246 = True => @lem5415128)). Qed.
Lemma lem5415131 : term246 = True.
Proof. exact (EQ_MP (@lem5415130) (@lem5415128)). Qed.
Lemma lem5415132 : term245 = True.
Proof. exact (TRANS (@lem5415127) (@lem5415131)). Qed.
Lemma lem5415133 : True = term245.
Proof. exact (SYM (@lem5415132)). Qed.
Lemma lem5415134 : term245.
Proof. exact (EQ_MP (@lem5415133) (@lem0)). Qed.
Lemma lem5415135 : term413 = term416.
Proof. exact (@lem5415124 (@lem5415134)). Qed.
Lemma lem5415137 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415138 : term223 = term224.
Proof. exact (@lem5415137 term69 term69). Qed.
Lemma lem5415139 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415140 : term226 = term69.
Proof. exact (EQ_MP (@lem5415139) (@lem940073)). Qed.
Lemma lem5415141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415142 : term224 = term170.
Proof. exact (MK_COMB (@lem5415141) (@lem5415140)). Qed.
Lemma lem5415143 : term223 = term170.
Proof. exact (TRANS (@lem5415138) (@lem5415142)). Qed.
Lemma lem5415145 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415146 : term418 = term153.
Proof. exact (@lem5415145 term69). Qed.
Lemma lem5415147 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415148 : term419 = term411.
Proof. exact (MK_COMB (@lem5415147) (@lem5415146)). Qed.
Lemma lem5415149 : term416 = term245.
Proof. exact (MK_COMB (@lem5415148) (@lem5415143)). Qed.
Lemma lem5415151 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415152 : term245 = term246.
Proof. exact (@lem5415151 (NUMERAL 0) term69). Qed.
Lemma lem5415153 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415154 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415155 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415154 h1) (fun h1 : term246 = True => @lem5415153)). Qed.
Lemma lem5415156 : term246 = True.
Proof. exact (EQ_MP (@lem5415155) (@lem5415153)). Qed.
Lemma lem5415157 : term245 = True.
Proof. exact (TRANS (@lem5415152) (@lem5415156)). Qed.
Lemma lem5415158 : term416 = True.
Proof. exact (TRANS (@lem5415149) (@lem5415157)). Qed.
Lemma lem5415159 : term413 = True.
Proof. exact (TRANS (@lem5415135) (@lem5415158)). Qed.
Lemma lem5415160 : term245 = True.
Proof. exact (TRANS (@lem5415112) (@lem5415159)). Qed.
Lemma lem5415161 : term410 = True.
Proof. exact (TRANS (@lem5415103) (@lem5415160)). Qed.
Lemma lem5415162 : True = term410.
Proof. exact (SYM (@lem5415161)). Qed.
Lemma lem5415163 : term410.
Proof. exact (EQ_MP (@lem5415162) (@lem0)). Qed.
Lemma lem5415164 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term426 _69909 _69910.
Proof. exact (conj (@lem5415163) (@lem5415022 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415166 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5415167 (_69909 : int) (_69910 : int) : term427 _69909 _69910.
Proof. exact (@lem5415166 term170 (term289 _69909 _69910)). Qed.
Lemma lem5415168 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term428 _69909 _69910.
Proof. exact (@lem5415167 _69909 _69910 (@lem5415164 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415169 (_69909 : int) (_69910 : int) : (term429 _69909 _69910) = (term289 _69909 _69910).
Proof. exact (@lem1982733 (term289 _69909 _69910)). Qed.
Lemma lem5415170 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415171 (_69909 : int) (_69910 : int) : (term430 _69909 _69910) = (term291 _69909 _69910).
Proof. exact (MK_COMB (@lem5415170) (@lem5415169 _69909 _69910)). Qed.
Lemma lem5415172 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415173 (_69909 : int) (_69910 : int) : (term428 _69909 _69910) = (term292 _69909 _69910).
Proof. exact (MK_COMB (@lem5415171 _69909 _69910) (@lem5415172)). Qed.
Lemma lem5415174 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term292 _69909 _69910.
Proof. exact (EQ_MP (@lem5415173 _69909 _69910) (@lem5415168 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415175 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term431 _69909 _69910 _69911.
Proof. exact (conj (@lem5415174 _69909 _69910 _69911 h1) (@lem5415100 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415177 (x : real) (y : real) : term432 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5415178 (_69909 : int) (_69910 : int) (_69911 : int) : term433 _69909 _69910 _69911.
Proof. exact (@lem5415177 (term289 _69909 _69910) (term317 _69910 _69911)). Qed.
Lemma lem5415179 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term434 _69909 _69910 _69911.
Proof. exact (@lem5415178 _69909 _69910 _69911 (@lem5415175 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415180 (_69909 : int) (_69910 : int) (_69911 : int) : (term435 _69909 _69910 _69911) = (term436 _69909 _69910 _69911).
Proof. exact (@lem1982755 (real_of_int _69909) (term288 _69910) (term317 _69910 _69911)). Qed.
Lemma lem5415181 (_69910 : int) (_69911 : int) : (term437 _69910 _69911) = (term438 _69910 _69911).
Proof. exact (@lem1982753 (term310 _69910) (real_of_int _69910) term283 (term310 _69911)). Qed.
Lemma lem5415182 (_69910 : int) : (term439 _69910) = (term440 _69910).
Proof. exact (@lem1982713 term214 (real_of_int _69910)). Qed.
Lemma lem5415184 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415185 : term170 = term237.
Proof. exact (@lem5415184 term69). Qed.
Lemma lem5415187 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5415188 : term214 = term215.
Proof. exact (@lem5415187 term69). Qed.
Lemma lem5415189 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415190 : term441 = term442.
Proof. exact (MK_COMB (@lem5415189) (@lem5415188)). Qed.
Lemma lem5415191 : term443 = term444.
Proof. exact (MK_COMB (@lem5415190) (@lem5415185)). Qed.
Lemma lem5415192 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5415194 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415195 : term245 = term246.
Proof. exact (@lem5415194 (NUMERAL 0) term69). Qed.
Lemma lem5415196 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415197 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415198 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415197 h1) (fun h1 : term246 = True => @lem5415196)). Qed.
Lemma lem5415199 : term246 = True.
Proof. exact (EQ_MP (@lem5415198) (@lem5415196)). Qed.
Lemma lem5415200 : term245 = True.
Proof. exact (TRANS (@lem5415195) (@lem5415199)). Qed.
Lemma lem5415201 : True = term245.
Proof. exact (SYM (@lem5415200)). Qed.
Lemma lem5415202 : term245.
Proof. exact (EQ_MP (@lem5415201) (@lem0)). Qed.
Lemma lem5415203 : term446.
Proof. exact (@lem5415192 (@lem5415202)). Qed.
Lemma lem5415205 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415206 : term245 = term246.
Proof. exact (@lem5415205 (NUMERAL 0) term69). Qed.
Lemma lem5415207 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415208 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415209 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415208 h1) (fun h1 : term246 = True => @lem5415207)). Qed.
Lemma lem5415210 : term246 = True.
Proof. exact (EQ_MP (@lem5415209) (@lem5415207)). Qed.
Lemma lem5415211 : term245 = True.
Proof. exact (TRANS (@lem5415206) (@lem5415210)). Qed.
Lemma lem5415212 : True = term245.
Proof. exact (SYM (@lem5415211)). Qed.
Lemma lem5415213 : term245.
Proof. exact (EQ_MP (@lem5415212) (@lem0)). Qed.
Lemma lem5415214 : term447.
Proof. exact (@lem5415203 (@lem5415213)). Qed.
Lemma lem5415216 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415217 : term245 = term246.
Proof. exact (@lem5415216 (NUMERAL 0) term69). Qed.
Lemma lem5415218 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415219 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415220 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415219 h1) (fun h1 : term246 = True => @lem5415218)). Qed.
Lemma lem5415221 : term246 = True.
Proof. exact (EQ_MP (@lem5415220) (@lem5415218)). Qed.
Lemma lem5415222 : term245 = True.
Proof. exact (TRANS (@lem5415217) (@lem5415221)). Qed.
Lemma lem5415223 : True = term245.
Proof. exact (SYM (@lem5415222)). Qed.
Lemma lem5415224 : term245.
Proof. exact (EQ_MP (@lem5415223) (@lem0)). Qed.
Lemma lem5415225 : term448.
Proof. exact (@lem5415214 (@lem5415224)). Qed.
Lemma lem5415227 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415228 : term223 = term224.
Proof. exact (@lem5415227 term69 term69). Qed.
Lemma lem5415229 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415230 : term226 = term69.
Proof. exact (EQ_MP (@lem5415229) (@lem940073)). Qed.
Lemma lem5415231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415232 : term224 = term170.
Proof. exact (MK_COMB (@lem5415231) (@lem5415230)). Qed.
Lemma lem5415233 : term223 = term170.
Proof. exact (TRANS (@lem5415228) (@lem5415232)). Qed.
Lemma lem5415235 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5415236 : term298 = term301.
Proof. exact (@lem5415235 term69 term69). Qed.
Lemma lem5415237 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415238 : term226 = term69.
Proof. exact (EQ_MP (@lem5415237) (@lem940073)). Qed.
Lemma lem5415239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415240 : term224 = term170.
Proof. exact (MK_COMB (@lem5415239) (@lem5415238)). Qed.
Lemma lem5415241 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5415242 : term301 = term214.
Proof. exact (MK_COMB (@lem5415241) (@lem5415240)). Qed.
Lemma lem5415243 : term298 = term214.
Proof. exact (TRANS (@lem5415236) (@lem5415242)). Qed.
Lemma lem5415244 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415245 : term449 = term441.
Proof. exact (MK_COMB (@lem5415244) (@lem5415243)). Qed.
Lemma lem5415246 : term450 = term443.
Proof. exact (MK_COMB (@lem5415245) (@lem5415233)). Qed.
Lemma lem5415248 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5415249 : term443 = term153.
Proof. exact (@lem5415248 term69). Qed.
Lemma lem5415250 : term450 = term153.
Proof. exact (TRANS (@lem5415246) (@lem5415249)). Qed.
Lemma lem5415251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5415252 : term452 = term453.
Proof. exact (MK_COMB (@lem5415251) (@lem5415250)). Qed.
Lemma lem5415253 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5415254 : term454 = term418.
Proof. exact (MK_COMB (@lem5415252) (@lem5415253)). Qed.
Lemma lem5415256 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415257 : term418 = term153.
Proof. exact (@lem5415256 term69). Qed.
Lemma lem5415258 : term454 = term153.
Proof. exact (TRANS (@lem5415254) (@lem5415257)). Qed.
Lemma lem5415260 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415261 : term223 = term224.
Proof. exact (@lem5415260 term69 term69). Qed.
Lemma lem5415262 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415263 : term226 = term69.
Proof. exact (EQ_MP (@lem5415262) (@lem940073)). Qed.
Lemma lem5415264 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415265 : term224 = term170.
Proof. exact (MK_COMB (@lem5415264) (@lem5415263)). Qed.
Lemma lem5415266 : term223 = term170.
Proof. exact (TRANS (@lem5415261) (@lem5415265)). Qed.
Lemma lem5415267 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5415268 : term455 = term418.
Proof. exact (MK_COMB (@lem5415267) (@lem5415266)). Qed.
Lemma lem5415270 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415271 : term418 = term153.
Proof. exact (@lem5415270 term69). Qed.
Lemma lem5415272 : term455 = term153.
Proof. exact (TRANS (@lem5415268) (@lem5415271)). Qed.
Lemma lem5415273 : term153 = term455.
Proof. exact (SYM (@lem5415272)). Qed.
Lemma lem5415274 : term454 = term455.
Proof. exact (TRANS (@lem5415258) (@lem5415273)). Qed.
Lemma lem5415275 : term444 = term211.
Proof. exact (@lem5415225 (@lem5415274)). Qed.
Lemma lem5415276 : term443 = term211.
Proof. exact (TRANS (@lem5415191) (@lem5415275)). Qed.
Lemma lem5415278 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5415279 : term211 = term153.
Proof. exact (@lem5415278 term153). Qed.
Lemma lem5415280 : term443 = term153.
Proof. exact (TRANS (@lem5415276) (@lem5415279)). Qed.
Lemma lem5415281 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5415282 : term456 = term453.
Proof. exact (MK_COMB (@lem5415281) (@lem5415280)). Qed.
Lemma lem5415283 (_69910 : int) : (real_of_int _69910) = (real_of_int _69910).
Proof. exact (eq_refl (real_of_int _69910)). Qed.
Lemma lem5415284 (_69910 : int) : (term440 _69910) = (term457 _69910).
Proof. exact (MK_COMB (@lem5415282) (@lem5415283 _69910)). Qed.
Lemma lem5415285 (_69910 : int) : (term439 _69910) = (term457 _69910).
Proof. exact (TRANS (@lem5415182 _69910) (@lem5415284 _69910)). Qed.
Lemma lem5415286 (_69910 : int) : (term457 _69910) = term153.
Proof. exact (@lem1982719 (real_of_int _69910)). Qed.
Lemma lem5415287 (_69910 : int) : (term439 _69910) = term153.
Proof. exact (TRANS (@lem5415285 _69910) (@lem5415286 _69910)). Qed.
Lemma lem5415288 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415289 (_69910 : int) : (term458 _69910) = term459.
Proof. exact (MK_COMB (@lem5415288) (@lem5415287 _69910)). Qed.
Lemma lem5415290 (_69911 : int) : (term460 _69911) = (term288 _69911).
Proof. exact (@lem1982761 (term310 _69911) term283). Qed.
Lemma lem5415291 (_69910 : int) (_69911 : int) : (term438 _69910 _69911) = (term461 _69911).
Proof. exact (MK_COMB (@lem5415289 _69910) (@lem5415290 _69911)). Qed.
Lemma lem5415292 (_69910 : int) (_69911 : int) : (term437 _69910 _69911) = (term461 _69911).
Proof. exact (TRANS (@lem5415181 _69910 _69911) (@lem5415291 _69910 _69911)). Qed.
Lemma lem5415293 (_69911 : int) : (term461 _69911) = (term288 _69911).
Proof. exact (@lem1982721 (term288 _69911)). Qed.
Lemma lem5415294 (_69910 : int) (_69911 : int) : (term437 _69910 _69911) = (term288 _69911).
Proof. exact (TRANS (@lem5415292 _69910 _69911) (@lem5415293 _69911)). Qed.
Lemma lem5415295 (_69909 : int) : (term171 _69909) = (term171 _69909).
Proof. exact (eq_refl (term171 _69909)). Qed.
Lemma lem5415296 (_69910 : int) (_69909 : int) (_69911 : int) : (term436 _69909 _69910 _69911) = (term289 _69909 _69911).
Proof. exact (MK_COMB (@lem5415295 _69909) (@lem5415294 _69910 _69911)). Qed.
Lemma lem5415297 (_69910 : int) (_69909 : int) (_69911 : int) : (term435 _69909 _69910 _69911) = (term289 _69909 _69911).
Proof. exact (TRANS (@lem5415180 _69909 _69910 _69911) (@lem5415296 _69910 _69909 _69911)). Qed.
Lemma lem5415298 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415299 (_69910 : int) (_69909 : int) (_69911 : int) : (term462 _69909 _69910 _69911) = (term291 _69909 _69911).
Proof. exact (MK_COMB (@lem5415298) (@lem5415297 _69910 _69909 _69911)). Qed.
Lemma lem5415300 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415301 (_69910 : int) (_69909 : int) (_69911 : int) : (term434 _69909 _69910 _69911) = (term292 _69909 _69911).
Proof. exact (MK_COMB (@lem5415299 _69910 _69909 _69911) (@lem5415300)). Qed.
Lemma lem5415302 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term292 _69909 _69911.
Proof. exact (EQ_MP (@lem5415301 _69910 _69909 _69911) (@lem5415179 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415304 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5415305 : term410 = term245.
Proof. exact (@lem5415304 term153 term170). Qed.
Lemma lem5415307 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415308 : term170 = term237.
Proof. exact (@lem5415307 term69). Qed.
Lemma lem5415310 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415311 : term153 = term211.
Proof. exact (@lem5415310 (NUMERAL 0)). Qed.
Lemma lem5415312 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415313 : term411 = term412.
Proof. exact (MK_COMB (@lem5415312) (@lem5415311)). Qed.
Lemma lem5415314 : term245 = term413.
Proof. exact (MK_COMB (@lem5415313) (@lem5415308)). Qed.
Lemma lem5415315 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5415317 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415318 : term245 = term246.
Proof. exact (@lem5415317 (NUMERAL 0) term69). Qed.
Lemma lem5415319 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415320 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415321 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415320 h1) (fun h1 : term246 = True => @lem5415319)). Qed.
Lemma lem5415322 : term246 = True.
Proof. exact (EQ_MP (@lem5415321) (@lem5415319)). Qed.
Lemma lem5415323 : term245 = True.
Proof. exact (TRANS (@lem5415318) (@lem5415322)). Qed.
Lemma lem5415324 : True = term245.
Proof. exact (SYM (@lem5415323)). Qed.
Lemma lem5415325 : term245.
Proof. exact (EQ_MP (@lem5415324) (@lem0)). Qed.
Lemma lem5415326 : term415.
Proof. exact (@lem5415315 (@lem5415325)). Qed.
Lemma lem5415328 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415329 : term245 = term246.
Proof. exact (@lem5415328 (NUMERAL 0) term69). Qed.
Lemma lem5415330 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415331 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415332 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415331 h1) (fun h1 : term246 = True => @lem5415330)). Qed.
Lemma lem5415333 : term246 = True.
Proof. exact (EQ_MP (@lem5415332) (@lem5415330)). Qed.
Lemma lem5415334 : term245 = True.
Proof. exact (TRANS (@lem5415329) (@lem5415333)). Qed.
Lemma lem5415335 : True = term245.
Proof. exact (SYM (@lem5415334)). Qed.
Lemma lem5415336 : term245.
Proof. exact (EQ_MP (@lem5415335) (@lem0)). Qed.
Lemma lem5415337 : term413 = term416.
Proof. exact (@lem5415326 (@lem5415336)). Qed.
Lemma lem5415339 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415340 : term223 = term224.
Proof. exact (@lem5415339 term69 term69). Qed.
Lemma lem5415341 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415342 : term226 = term69.
Proof. exact (EQ_MP (@lem5415341) (@lem940073)). Qed.
Lemma lem5415343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415344 : term224 = term170.
Proof. exact (MK_COMB (@lem5415343) (@lem5415342)). Qed.
Lemma lem5415345 : term223 = term170.
Proof. exact (TRANS (@lem5415340) (@lem5415344)). Qed.
Lemma lem5415347 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415348 : term418 = term153.
Proof. exact (@lem5415347 term69). Qed.
Lemma lem5415349 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415350 : term419 = term411.
Proof. exact (MK_COMB (@lem5415349) (@lem5415348)). Qed.
Lemma lem5415351 : term416 = term245.
Proof. exact (MK_COMB (@lem5415350) (@lem5415345)). Qed.
Lemma lem5415353 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415354 : term245 = term246.
Proof. exact (@lem5415353 (NUMERAL 0) term69). Qed.
Lemma lem5415355 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415356 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415357 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415356 h1) (fun h1 : term246 = True => @lem5415355)). Qed.
Lemma lem5415358 : term246 = True.
Proof. exact (EQ_MP (@lem5415357) (@lem5415355)). Qed.
Lemma lem5415359 : term245 = True.
Proof. exact (TRANS (@lem5415354) (@lem5415358)). Qed.
Lemma lem5415360 : term416 = True.
Proof. exact (TRANS (@lem5415351) (@lem5415359)). Qed.
Lemma lem5415361 : term413 = True.
Proof. exact (TRANS (@lem5415337) (@lem5415360)). Qed.
Lemma lem5415362 : term245 = True.
Proof. exact (TRANS (@lem5415314) (@lem5415361)). Qed.
Lemma lem5415363 : term410 = True.
Proof. exact (TRANS (@lem5415305) (@lem5415362)). Qed.
Lemma lem5415364 : True = term410.
Proof. exact (SYM (@lem5415363)). Qed.
Lemma lem5415365 : term410.
Proof. exact (EQ_MP (@lem5415364) (@lem0)). Qed.
Lemma lem5415366 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term426 _69909 _69911.
Proof. exact (conj (@lem5415365) (@lem5415302 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415368 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5415369 (_69909 : int) (_69911 : int) : term427 _69909 _69911.
Proof. exact (@lem5415368 term170 (term289 _69909 _69911)). Qed.
Lemma lem5415370 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term428 _69909 _69911.
Proof. exact (@lem5415369 _69909 _69911 (@lem5415366 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415371 (_69909 : int) (_69911 : int) : (term429 _69909 _69911) = (term289 _69909 _69911).
Proof. exact (@lem1982733 (term289 _69909 _69911)). Qed.
Lemma lem5415372 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415373 (_69909 : int) (_69911 : int) : (term430 _69909 _69911) = (term291 _69909 _69911).
Proof. exact (MK_COMB (@lem5415372) (@lem5415371 _69909 _69911)). Qed.
Lemma lem5415374 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415375 (_69909 : int) (_69911 : int) : (term428 _69909 _69911) = (term292 _69909 _69911).
Proof. exact (MK_COMB (@lem5415373 _69909 _69911) (@lem5415374)). Qed.
Lemma lem5415376 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term292 _69909 _69911.
Proof. exact (EQ_MP (@lem5415375 _69909 _69911) (@lem5415370 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415378 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5415379 : term410 = term245.
Proof. exact (@lem5415378 term153 term170). Qed.
Lemma lem5415381 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415382 : term170 = term237.
Proof. exact (@lem5415381 term69). Qed.
Lemma lem5415384 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415385 : term153 = term211.
Proof. exact (@lem5415384 (NUMERAL 0)). Qed.
Lemma lem5415386 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415387 : term411 = term412.
Proof. exact (MK_COMB (@lem5415386) (@lem5415385)). Qed.
Lemma lem5415388 : term245 = term413.
Proof. exact (MK_COMB (@lem5415387) (@lem5415382)). Qed.
Lemma lem5415389 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5415391 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415392 : term245 = term246.
Proof. exact (@lem5415391 (NUMERAL 0) term69). Qed.
Lemma lem5415393 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415394 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415395 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415394 h1) (fun h1 : term246 = True => @lem5415393)). Qed.
Lemma lem5415396 : term246 = True.
Proof. exact (EQ_MP (@lem5415395) (@lem5415393)). Qed.
Lemma lem5415397 : term245 = True.
Proof. exact (TRANS (@lem5415392) (@lem5415396)). Qed.
Lemma lem5415398 : True = term245.
Proof. exact (SYM (@lem5415397)). Qed.
Lemma lem5415399 : term245.
Proof. exact (EQ_MP (@lem5415398) (@lem0)). Qed.
Lemma lem5415400 : term415.
Proof. exact (@lem5415389 (@lem5415399)). Qed.
Lemma lem5415402 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415403 : term245 = term246.
Proof. exact (@lem5415402 (NUMERAL 0) term69). Qed.
Lemma lem5415404 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415405 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415406 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415405 h1) (fun h1 : term246 = True => @lem5415404)). Qed.
Lemma lem5415407 : term246 = True.
Proof. exact (EQ_MP (@lem5415406) (@lem5415404)). Qed.
Lemma lem5415408 : term245 = True.
Proof. exact (TRANS (@lem5415403) (@lem5415407)). Qed.
Lemma lem5415409 : True = term245.
Proof. exact (SYM (@lem5415408)). Qed.
Lemma lem5415410 : term245.
Proof. exact (EQ_MP (@lem5415409) (@lem0)). Qed.
Lemma lem5415411 : term413 = term416.
Proof. exact (@lem5415400 (@lem5415410)). Qed.
Lemma lem5415413 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415414 : term223 = term224.
Proof. exact (@lem5415413 term69 term69). Qed.
Lemma lem5415415 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415416 : term226 = term69.
Proof. exact (EQ_MP (@lem5415415) (@lem940073)). Qed.
Lemma lem5415417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415418 : term224 = term170.
Proof. exact (MK_COMB (@lem5415417) (@lem5415416)). Qed.
Lemma lem5415419 : term223 = term170.
Proof. exact (TRANS (@lem5415414) (@lem5415418)). Qed.
Lemma lem5415421 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415422 : term418 = term153.
Proof. exact (@lem5415421 term69). Qed.
Lemma lem5415423 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415424 : term419 = term411.
Proof. exact (MK_COMB (@lem5415423) (@lem5415422)). Qed.
Lemma lem5415425 : term416 = term245.
Proof. exact (MK_COMB (@lem5415424) (@lem5415419)). Qed.
Lemma lem5415427 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415428 : term245 = term246.
Proof. exact (@lem5415427 (NUMERAL 0) term69). Qed.
Lemma lem5415429 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415430 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415431 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415430 h1) (fun h1 : term246 = True => @lem5415429)). Qed.
Lemma lem5415432 : term246 = True.
Proof. exact (EQ_MP (@lem5415431) (@lem5415429)). Qed.
Lemma lem5415433 : term245 = True.
Proof. exact (TRANS (@lem5415428) (@lem5415432)). Qed.
Lemma lem5415434 : term416 = True.
Proof. exact (TRANS (@lem5415425) (@lem5415433)). Qed.
Lemma lem5415435 : term413 = True.
Proof. exact (TRANS (@lem5415411) (@lem5415434)). Qed.
Lemma lem5415436 : term245 = True.
Proof. exact (TRANS (@lem5415388) (@lem5415435)). Qed.
Lemma lem5415437 : term410 = True.
Proof. exact (TRANS (@lem5415379) (@lem5415436)). Qed.
Lemma lem5415438 : True = term410.
Proof. exact (SYM (@lem5415437)). Qed.
Lemma lem5415439 : term410.
Proof. exact (EQ_MP (@lem5415438) (@lem0)). Qed.
Lemma lem5415440 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term463 _69909 _69911.
Proof. exact (conj (@lem5415439) (@lem5415026 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415442 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5415443 (_69909 : int) (_69911 : int) : term464 _69909 _69911.
Proof. exact (@lem5415442 term170 (term318 _69909 _69911)). Qed.
Lemma lem5415444 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term465 _69909 _69911.
Proof. exact (@lem5415443 _69909 _69911 (@lem5415440 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415445 (_69909 : int) (_69911 : int) : (term466 _69909 _69911) = (term318 _69909 _69911).
Proof. exact (@lem1982733 (term318 _69909 _69911)). Qed.
Lemma lem5415446 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415447 (_69909 : int) (_69911 : int) : (term467 _69909 _69911) = (term320 _69909 _69911).
Proof. exact (MK_COMB (@lem5415446) (@lem5415445 _69909 _69911)). Qed.
Lemma lem5415448 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415449 (_69909 : int) (_69911 : int) : (term465 _69909 _69911) = (term321 _69909 _69911).
Proof. exact (MK_COMB (@lem5415447 _69909 _69911) (@lem5415448)). Qed.
Lemma lem5415450 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term321 _69909 _69911.
Proof. exact (EQ_MP (@lem5415449 _69909 _69911) (@lem5415444 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415451 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term468 _69909 _69911.
Proof. exact (conj (@lem5415450 _69909 _69910 _69911 h1) (@lem5415376 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415453 (x : real) (y : real) : term432 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5415454 (_69909 : int) (_69911 : int) : term469 _69909 _69911.
Proof. exact (@lem5415453 (term318 _69909 _69911) (term289 _69909 _69911)). Qed.
Lemma lem5415455 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term470 _69909 _69911.
Proof. exact (@lem5415454 _69909 _69911 (@lem5415451 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415456 (_69909 : int) (_69911 : int) : (term471 _69909 _69911) = (term472 _69909 _69911).
Proof. exact (@lem1982753 (term310 _69909) (real_of_int _69909) (real_of_int _69911) (term288 _69911)). Qed.
Lemma lem5415457 (_69909 : int) : (term439 _69909) = (term440 _69909).
Proof. exact (@lem1982713 term214 (real_of_int _69909)). Qed.
Lemma lem5415459 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415460 : term170 = term237.
Proof. exact (@lem5415459 term69). Qed.
Lemma lem5415462 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5415463 : term214 = term215.
Proof. exact (@lem5415462 term69). Qed.
Lemma lem5415464 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415465 : term441 = term442.
Proof. exact (MK_COMB (@lem5415464) (@lem5415463)). Qed.
Lemma lem5415466 : term443 = term444.
Proof. exact (MK_COMB (@lem5415465) (@lem5415460)). Qed.
Lemma lem5415467 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5415469 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415470 : term245 = term246.
Proof. exact (@lem5415469 (NUMERAL 0) term69). Qed.
Lemma lem5415471 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415472 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415473 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415472 h1) (fun h1 : term246 = True => @lem5415471)). Qed.
Lemma lem5415474 : term246 = True.
Proof. exact (EQ_MP (@lem5415473) (@lem5415471)). Qed.
Lemma lem5415475 : term245 = True.
Proof. exact (TRANS (@lem5415470) (@lem5415474)). Qed.
Lemma lem5415476 : True = term245.
Proof. exact (SYM (@lem5415475)). Qed.
Lemma lem5415477 : term245.
Proof. exact (EQ_MP (@lem5415476) (@lem0)). Qed.
Lemma lem5415478 : term446.
Proof. exact (@lem5415467 (@lem5415477)). Qed.
Lemma lem5415480 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415481 : term245 = term246.
Proof. exact (@lem5415480 (NUMERAL 0) term69). Qed.
Lemma lem5415482 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415483 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415484 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415483 h1) (fun h1 : term246 = True => @lem5415482)). Qed.
Lemma lem5415485 : term246 = True.
Proof. exact (EQ_MP (@lem5415484) (@lem5415482)). Qed.
Lemma lem5415486 : term245 = True.
Proof. exact (TRANS (@lem5415481) (@lem5415485)). Qed.
Lemma lem5415487 : True = term245.
Proof. exact (SYM (@lem5415486)). Qed.
Lemma lem5415488 : term245.
Proof. exact (EQ_MP (@lem5415487) (@lem0)). Qed.
Lemma lem5415489 : term447.
Proof. exact (@lem5415478 (@lem5415488)). Qed.
Lemma lem5415491 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415492 : term245 = term246.
Proof. exact (@lem5415491 (NUMERAL 0) term69). Qed.
Lemma lem5415493 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415494 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415495 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415494 h1) (fun h1 : term246 = True => @lem5415493)). Qed.
Lemma lem5415496 : term246 = True.
Proof. exact (EQ_MP (@lem5415495) (@lem5415493)). Qed.
Lemma lem5415497 : term245 = True.
Proof. exact (TRANS (@lem5415492) (@lem5415496)). Qed.
Lemma lem5415498 : True = term245.
Proof. exact (SYM (@lem5415497)). Qed.
Lemma lem5415499 : term245.
Proof. exact (EQ_MP (@lem5415498) (@lem0)). Qed.
Lemma lem5415500 : term448.
Proof. exact (@lem5415489 (@lem5415499)). Qed.
Lemma lem5415502 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415503 : term223 = term224.
Proof. exact (@lem5415502 term69 term69). Qed.
Lemma lem5415504 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415505 : term226 = term69.
Proof. exact (EQ_MP (@lem5415504) (@lem940073)). Qed.
Lemma lem5415506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415507 : term224 = term170.
Proof. exact (MK_COMB (@lem5415506) (@lem5415505)). Qed.
Lemma lem5415508 : term223 = term170.
Proof. exact (TRANS (@lem5415503) (@lem5415507)). Qed.
Lemma lem5415510 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5415511 : term298 = term301.
Proof. exact (@lem5415510 term69 term69). Qed.
Lemma lem5415512 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415513 : term226 = term69.
Proof. exact (EQ_MP (@lem5415512) (@lem940073)). Qed.
Lemma lem5415514 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415515 : term224 = term170.
Proof. exact (MK_COMB (@lem5415514) (@lem5415513)). Qed.
Lemma lem5415516 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5415517 : term301 = term214.
Proof. exact (MK_COMB (@lem5415516) (@lem5415515)). Qed.
Lemma lem5415518 : term298 = term214.
Proof. exact (TRANS (@lem5415511) (@lem5415517)). Qed.
Lemma lem5415519 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415520 : term449 = term441.
Proof. exact (MK_COMB (@lem5415519) (@lem5415518)). Qed.
Lemma lem5415521 : term450 = term443.
Proof. exact (MK_COMB (@lem5415520) (@lem5415508)). Qed.
Lemma lem5415523 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5415524 : term443 = term153.
Proof. exact (@lem5415523 term69). Qed.
Lemma lem5415525 : term450 = term153.
Proof. exact (TRANS (@lem5415521) (@lem5415524)). Qed.
Lemma lem5415526 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5415527 : term452 = term453.
Proof. exact (MK_COMB (@lem5415526) (@lem5415525)). Qed.
Lemma lem5415528 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5415529 : term454 = term418.
Proof. exact (MK_COMB (@lem5415527) (@lem5415528)). Qed.
Lemma lem5415531 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415532 : term418 = term153.
Proof. exact (@lem5415531 term69). Qed.
Lemma lem5415533 : term454 = term153.
Proof. exact (TRANS (@lem5415529) (@lem5415532)). Qed.
Lemma lem5415535 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415536 : term223 = term224.
Proof. exact (@lem5415535 term69 term69). Qed.
Lemma lem5415537 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415538 : term226 = term69.
Proof. exact (EQ_MP (@lem5415537) (@lem940073)). Qed.
Lemma lem5415539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415540 : term224 = term170.
Proof. exact (MK_COMB (@lem5415539) (@lem5415538)). Qed.
Lemma lem5415541 : term223 = term170.
Proof. exact (TRANS (@lem5415536) (@lem5415540)). Qed.
Lemma lem5415542 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5415543 : term455 = term418.
Proof. exact (MK_COMB (@lem5415542) (@lem5415541)). Qed.
Lemma lem5415545 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415546 : term418 = term153.
Proof. exact (@lem5415545 term69). Qed.
Lemma lem5415547 : term455 = term153.
Proof. exact (TRANS (@lem5415543) (@lem5415546)). Qed.
Lemma lem5415548 : term153 = term455.
Proof. exact (SYM (@lem5415547)). Qed.
Lemma lem5415549 : term454 = term455.
Proof. exact (TRANS (@lem5415533) (@lem5415548)). Qed.
Lemma lem5415550 : term444 = term211.
Proof. exact (@lem5415500 (@lem5415549)). Qed.
Lemma lem5415551 : term443 = term211.
Proof. exact (TRANS (@lem5415466) (@lem5415550)). Qed.
Lemma lem5415553 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5415554 : term211 = term153.
Proof. exact (@lem5415553 term153). Qed.
Lemma lem5415555 : term443 = term153.
Proof. exact (TRANS (@lem5415551) (@lem5415554)). Qed.
Lemma lem5415556 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5415557 : term456 = term453.
Proof. exact (MK_COMB (@lem5415556) (@lem5415555)). Qed.
Lemma lem5415558 (_69909 : int) : (real_of_int _69909) = (real_of_int _69909).
Proof. exact (eq_refl (real_of_int _69909)). Qed.
Lemma lem5415559 (_69909 : int) : (term440 _69909) = (term457 _69909).
Proof. exact (MK_COMB (@lem5415557) (@lem5415558 _69909)). Qed.
Lemma lem5415560 (_69909 : int) : (term439 _69909) = (term457 _69909).
Proof. exact (TRANS (@lem5415457 _69909) (@lem5415559 _69909)). Qed.
Lemma lem5415561 (_69909 : int) : (term457 _69909) = term153.
Proof. exact (@lem1982719 (real_of_int _69909)). Qed.
Lemma lem5415562 (_69909 : int) : (term439 _69909) = term153.
Proof. exact (TRANS (@lem5415560 _69909) (@lem5415561 _69909)). Qed.
Lemma lem5415563 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415564 (_69909 : int) : (term458 _69909) = term459.
Proof. exact (MK_COMB (@lem5415563) (@lem5415562 _69909)). Qed.
Lemma lem5415565 (_69911 : int) : (term473 _69911) = (term474 _69911).
Proof. exact (@lem1982763 (real_of_int _69911) (term310 _69911) term283). Qed.
Lemma lem5415566 (_69911 : int) : (term475 _69911) = (term440 _69911).
Proof. exact (@lem1982715 term214 (real_of_int _69911)). Qed.
Lemma lem5415568 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415569 : term170 = term237.
Proof. exact (@lem5415568 term69). Qed.
Lemma lem5415571 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5415572 : term214 = term215.
Proof. exact (@lem5415571 term69). Qed.
Lemma lem5415573 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415574 : term441 = term442.
Proof. exact (MK_COMB (@lem5415573) (@lem5415572)). Qed.
Lemma lem5415575 : term443 = term444.
Proof. exact (MK_COMB (@lem5415574) (@lem5415569)). Qed.
Lemma lem5415576 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5415578 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415579 : term245 = term246.
Proof. exact (@lem5415578 (NUMERAL 0) term69). Qed.
Lemma lem5415580 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415581 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415582 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415581 h1) (fun h1 : term246 = True => @lem5415580)). Qed.
Lemma lem5415583 : term246 = True.
Proof. exact (EQ_MP (@lem5415582) (@lem5415580)). Qed.
Lemma lem5415584 : term245 = True.
Proof. exact (TRANS (@lem5415579) (@lem5415583)). Qed.
Lemma lem5415585 : True = term245.
Proof. exact (SYM (@lem5415584)). Qed.
Lemma lem5415586 : term245.
Proof. exact (EQ_MP (@lem5415585) (@lem0)). Qed.
Lemma lem5415587 : term446.
Proof. exact (@lem5415576 (@lem5415586)). Qed.
Lemma lem5415589 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415590 : term245 = term246.
Proof. exact (@lem5415589 (NUMERAL 0) term69). Qed.
Lemma lem5415591 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415592 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415593 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415592 h1) (fun h1 : term246 = True => @lem5415591)). Qed.
Lemma lem5415594 : term246 = True.
Proof. exact (EQ_MP (@lem5415593) (@lem5415591)). Qed.
Lemma lem5415595 : term245 = True.
Proof. exact (TRANS (@lem5415590) (@lem5415594)). Qed.
Lemma lem5415596 : True = term245.
Proof. exact (SYM (@lem5415595)). Qed.
Lemma lem5415597 : term245.
Proof. exact (EQ_MP (@lem5415596) (@lem0)). Qed.
Lemma lem5415598 : term447.
Proof. exact (@lem5415587 (@lem5415597)). Qed.
Lemma lem5415600 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415601 : term245 = term246.
Proof. exact (@lem5415600 (NUMERAL 0) term69). Qed.
Lemma lem5415602 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415603 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415604 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415603 h1) (fun h1 : term246 = True => @lem5415602)). Qed.
Lemma lem5415605 : term246 = True.
Proof. exact (EQ_MP (@lem5415604) (@lem5415602)). Qed.
Lemma lem5415606 : term245 = True.
Proof. exact (TRANS (@lem5415601) (@lem5415605)). Qed.
Lemma lem5415607 : True = term245.
Proof. exact (SYM (@lem5415606)). Qed.
Lemma lem5415608 : term245.
Proof. exact (EQ_MP (@lem5415607) (@lem0)). Qed.
Lemma lem5415609 : term448.
Proof. exact (@lem5415598 (@lem5415608)). Qed.
Lemma lem5415611 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415612 : term223 = term224.
Proof. exact (@lem5415611 term69 term69). Qed.
Lemma lem5415613 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415614 : term226 = term69.
Proof. exact (EQ_MP (@lem5415613) (@lem940073)). Qed.
Lemma lem5415615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415616 : term224 = term170.
Proof. exact (MK_COMB (@lem5415615) (@lem5415614)). Qed.
Lemma lem5415617 : term223 = term170.
Proof. exact (TRANS (@lem5415612) (@lem5415616)). Qed.
Lemma lem5415619 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5415620 : term298 = term301.
Proof. exact (@lem5415619 term69 term69). Qed.
Lemma lem5415621 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415622 : term226 = term69.
Proof. exact (EQ_MP (@lem5415621) (@lem940073)). Qed.
Lemma lem5415623 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415624 : term224 = term170.
Proof. exact (MK_COMB (@lem5415623) (@lem5415622)). Qed.
Lemma lem5415625 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5415626 : term301 = term214.
Proof. exact (MK_COMB (@lem5415625) (@lem5415624)). Qed.
Lemma lem5415627 : term298 = term214.
Proof. exact (TRANS (@lem5415620) (@lem5415626)). Qed.
Lemma lem5415628 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415629 : term449 = term441.
Proof. exact (MK_COMB (@lem5415628) (@lem5415627)). Qed.
Lemma lem5415630 : term450 = term443.
Proof. exact (MK_COMB (@lem5415629) (@lem5415617)). Qed.
Lemma lem5415632 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5415633 : term443 = term153.
Proof. exact (@lem5415632 term69). Qed.
Lemma lem5415634 : term450 = term153.
Proof. exact (TRANS (@lem5415630) (@lem5415633)). Qed.
Lemma lem5415635 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5415636 : term452 = term453.
Proof. exact (MK_COMB (@lem5415635) (@lem5415634)). Qed.
Lemma lem5415637 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5415638 : term454 = term418.
Proof. exact (MK_COMB (@lem5415636) (@lem5415637)). Qed.
Lemma lem5415640 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415641 : term418 = term153.
Proof. exact (@lem5415640 term69). Qed.
Lemma lem5415642 : term454 = term153.
Proof. exact (TRANS (@lem5415638) (@lem5415641)). Qed.
Lemma lem5415644 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415645 : term223 = term224.
Proof. exact (@lem5415644 term69 term69). Qed.
Lemma lem5415646 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415647 : term226 = term69.
Proof. exact (EQ_MP (@lem5415646) (@lem940073)). Qed.
Lemma lem5415648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415649 : term224 = term170.
Proof. exact (MK_COMB (@lem5415648) (@lem5415647)). Qed.
Lemma lem5415650 : term223 = term170.
Proof. exact (TRANS (@lem5415645) (@lem5415649)). Qed.
Lemma lem5415651 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5415652 : term455 = term418.
Proof. exact (MK_COMB (@lem5415651) (@lem5415650)). Qed.
Lemma lem5415654 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415655 : term418 = term153.
Proof. exact (@lem5415654 term69). Qed.
Lemma lem5415656 : term455 = term153.
Proof. exact (TRANS (@lem5415652) (@lem5415655)). Qed.
Lemma lem5415657 : term153 = term455.
Proof. exact (SYM (@lem5415656)). Qed.
Lemma lem5415658 : term454 = term455.
Proof. exact (TRANS (@lem5415642) (@lem5415657)). Qed.
Lemma lem5415659 : term444 = term211.
Proof. exact (@lem5415609 (@lem5415658)). Qed.
Lemma lem5415660 : term443 = term211.
Proof. exact (TRANS (@lem5415575) (@lem5415659)). Qed.
Lemma lem5415662 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5415663 : term211 = term153.
Proof. exact (@lem5415662 term153). Qed.
Lemma lem5415664 : term443 = term153.
Proof. exact (TRANS (@lem5415660) (@lem5415663)). Qed.
Lemma lem5415665 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5415666 : term456 = term453.
Proof. exact (MK_COMB (@lem5415665) (@lem5415664)). Qed.
Lemma lem5415667 (_69911 : int) : (real_of_int _69911) = (real_of_int _69911).
Proof. exact (eq_refl (real_of_int _69911)). Qed.
Lemma lem5415668 (_69911 : int) : (term440 _69911) = (term457 _69911).
Proof. exact (MK_COMB (@lem5415666) (@lem5415667 _69911)). Qed.
Lemma lem5415669 (_69911 : int) : (term475 _69911) = (term457 _69911).
Proof. exact (TRANS (@lem5415566 _69911) (@lem5415668 _69911)). Qed.
Lemma lem5415670 (_69911 : int) : (term457 _69911) = term153.
Proof. exact (@lem1982719 (real_of_int _69911)). Qed.
Lemma lem5415671 (_69911 : int) : (term475 _69911) = term153.
Proof. exact (TRANS (@lem5415669 _69911) (@lem5415670 _69911)). Qed.
Lemma lem5415672 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5415673 (_69911 : int) : (term476 _69911) = term459.
Proof. exact (MK_COMB (@lem5415672) (@lem5415671 _69911)). Qed.
Lemma lem5415674 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem5415675 (_69911 : int) : (term474 _69911) = term477.
Proof. exact (MK_COMB (@lem5415673 _69911) (@lem5415674)). Qed.
Lemma lem5415676 (_69911 : int) : (term473 _69911) = term477.
Proof. exact (TRANS (@lem5415565 _69911) (@lem5415675 _69911)). Qed.
Lemma lem5415677 : term477 = term283.
Proof. exact (@lem1982721 term283). Qed.
Lemma lem5415678 (_69911 : int) : (term473 _69911) = term283.
Proof. exact (TRANS (@lem5415676 _69911) (@lem5415677)). Qed.
Lemma lem5415679 (_69909 : int) (_69911 : int) : (term472 _69909 _69911) = term477.
Proof. exact (MK_COMB (@lem5415564 _69909) (@lem5415678 _69911)). Qed.
Lemma lem5415680 (_69909 : int) (_69911 : int) : (term471 _69909 _69911) = term477.
Proof. exact (TRANS (@lem5415456 _69909 _69911) (@lem5415679 _69909 _69911)). Qed.
Lemma lem5415681 : term477 = term283.
Proof. exact (@lem1982721 term283). Qed.
Lemma lem5415682 (_69909 : int) (_69911 : int) : (term471 _69909 _69911) = term283.
Proof. exact (TRANS (@lem5415680 _69909 _69911) (@lem5415681)). Qed.
Lemma lem5415683 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415684 (_69909 : int) (_69911 : int) : (term478 _69909 _69911) = term479.
Proof. exact (MK_COMB (@lem5415683) (@lem5415682 _69909 _69911)). Qed.
Lemma lem5415685 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415686 (_69909 : int) (_69911 : int) : (term470 _69909 _69911) = term480.
Proof. exact (MK_COMB (@lem5415684 _69909 _69911) (@lem5415685)). Qed.
Lemma lem5415687 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : term480.
Proof. exact (EQ_MP (@lem5415686 _69909 _69911) (@lem5415455 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415689 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5415690 : term480 = term481.
Proof. exact (@lem5415689 term153 term283). Qed.
Lemma lem5415692 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5415693 : term283 = term286.
Proof. exact (@lem5415692 term257). Qed.
Lemma lem5415695 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415696 : term153 = term211.
Proof. exact (@lem5415695 (NUMERAL 0)). Qed.
Lemma lem5415697 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5415698 : term155 = term482.
Proof. exact (MK_COMB (@lem5415697) (@lem5415696)). Qed.
Lemma lem5415699 : term481 = term483.
Proof. exact (MK_COMB (@lem5415698) (@lem5415693)). Qed.
Lemma lem5415700 : term484.
Proof. exact (@lem1980026 term153 term170 term283 term170). Qed.
Lemma lem5415702 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415703 : term245 = term246.
Proof. exact (@lem5415702 (NUMERAL 0) term69). Qed.
Lemma lem5415704 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415705 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415706 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415705 h1) (fun h1 : term246 = True => @lem5415704)). Qed.
Lemma lem5415707 : term246 = True.
Proof. exact (EQ_MP (@lem5415706) (@lem5415704)). Qed.
Lemma lem5415708 : term245 = True.
Proof. exact (TRANS (@lem5415703) (@lem5415707)). Qed.
Lemma lem5415709 : True = term245.
Proof. exact (SYM (@lem5415708)). Qed.
Lemma lem5415710 : term245.
Proof. exact (EQ_MP (@lem5415709) (@lem0)). Qed.
Lemma lem5415711 : term485.
Proof. exact (@lem5415700 (@lem5415710)). Qed.
Lemma lem5415713 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415714 : term245 = term246.
Proof. exact (@lem5415713 (NUMERAL 0) term69). Qed.
Lemma lem5415715 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415716 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415717 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415716 h1) (fun h1 : term246 = True => @lem5415715)). Qed.
Lemma lem5415718 : term246 = True.
Proof. exact (EQ_MP (@lem5415717) (@lem5415715)). Qed.
Lemma lem5415719 : term245 = True.
Proof. exact (TRANS (@lem5415714) (@lem5415718)). Qed.
Lemma lem5415720 : True = term245.
Proof. exact (SYM (@lem5415719)). Qed.
Lemma lem5415721 : term245.
Proof. exact (EQ_MP (@lem5415720) (@lem0)). Qed.
Lemma lem5415722 : term483 = term486.
Proof. exact (@lem5415711 (@lem5415721)). Qed.
Lemma lem5415724 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5415725 : term487 = term488.
Proof. exact (@lem5415724 term257 term69). Qed.
Lemma lem5415726 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5415727 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5415728 : term264 = term257.
Proof. exact (EQ_MP (@lem5415727) (@lem5415726)). Qed.
Lemma lem5415729 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415730 : term262 = term243.
Proof. exact (MK_COMB (@lem5415729) (@lem5415728)). Qed.
Lemma lem5415731 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5415732 : term488 = term283.
Proof. exact (MK_COMB (@lem5415731) (@lem5415730)). Qed.
Lemma lem5415733 : term487 = term283.
Proof. exact (TRANS (@lem5415725) (@lem5415732)). Qed.
Lemma lem5415735 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415736 : term418 = term153.
Proof. exact (@lem5415735 term69). Qed.
Lemma lem5415737 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5415738 : term489 = term155.
Proof. exact (MK_COMB (@lem5415737) (@lem5415736)). Qed.
Lemma lem5415739 : term486 = term481.
Proof. exact (MK_COMB (@lem5415738) (@lem5415733)). Qed.
Lemma lem5415741 (m : nat) (n : nat) : (term490 m n) = (term491 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5415742 : term481 = term492.
Proof. exact (@lem5415741 (NUMERAL 0) term257). Qed.
Lemma lem5415743 : term493 = term255.
Proof. exact (@lem912803). Qed.
Lemma lem5415744 (h1 : term493 = term255) : (term257 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term255 h1). Qed.
Lemma lem5415745 : (term493 = term255) = ((term257 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term493 = term255 => @lem5415744 h1) (fun h1 : (term257 = (NUMERAL 0)) = False => @lem5415743)). Qed.
Lemma lem5415746 : (term257 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5415745) (@lem5415743)). Qed.
Lemma lem5415747 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5415748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5415749 : term494 = (and True).
Proof. exact (MK_COMB (@lem5415748) (@lem5415747)). Qed.
Lemma lem5415750 : term492 = (True /\ False).
Proof. exact (MK_COMB (@lem5415749) (@lem5415746)). Qed.
Lemma lem5415752 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5415753 : term492 = False.
Proof. exact (TRANS (@lem5415750) (@lem5415752)). Qed.
Lemma lem5415754 : term481 = False.
Proof. exact (TRANS (@lem5415742) (@lem5415753)). Qed.
Lemma lem5415755 : term486 = False.
Proof. exact (TRANS (@lem5415739) (@lem5415754)). Qed.
Lemma lem5415756 : term483 = False.
Proof. exact (TRANS (@lem5415722) (@lem5415755)). Qed.
Lemma lem5415757 : term481 = False.
Proof. exact (TRANS (@lem5415699) (@lem5415756)). Qed.
Lemma lem5415758 : term480 = False.
Proof. exact (TRANS (@lem5415690) (@lem5415757)). Qed.
Lemma lem5415759 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term409 _69909 _69910 _69911) : False.
Proof. exact (EQ_MP (@lem5415758) (@lem5415687 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415760 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term495 _69909 _69910 _69911.
Proof. exact (h1). Qed.
Lemma lem5415761 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term405 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415760 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415763 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term392 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415761 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415765 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term379 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415763 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415767 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term366 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415765 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415768 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term292 _69909 _69910.
Proof. exact (proj1 (@lem5415765 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415769 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term325 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5415767 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415771 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term323 _69910 _69911.
Proof. exact (proj2 (@lem5415769 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415772 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term321 _69909 _69911.
Proof. exact (proj1 (@lem5415769 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415774 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5415775 : term410 = term245.
Proof. exact (@lem5415774 term153 term170). Qed.
Lemma lem5415777 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415778 : term170 = term237.
Proof. exact (@lem5415777 term69). Qed.
Lemma lem5415780 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415781 : term153 = term211.
Proof. exact (@lem5415780 (NUMERAL 0)). Qed.
Lemma lem5415782 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415783 : term411 = term412.
Proof. exact (MK_COMB (@lem5415782) (@lem5415781)). Qed.
Lemma lem5415784 : term245 = term413.
Proof. exact (MK_COMB (@lem5415783) (@lem5415778)). Qed.
Lemma lem5415785 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5415787 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415788 : term245 = term246.
Proof. exact (@lem5415787 (NUMERAL 0) term69). Qed.
Lemma lem5415789 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415790 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415791 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415790 h1) (fun h1 : term246 = True => @lem5415789)). Qed.
Lemma lem5415792 : term246 = True.
Proof. exact (EQ_MP (@lem5415791) (@lem5415789)). Qed.
Lemma lem5415793 : term245 = True.
Proof. exact (TRANS (@lem5415788) (@lem5415792)). Qed.
Lemma lem5415794 : True = term245.
Proof. exact (SYM (@lem5415793)). Qed.
Lemma lem5415795 : term245.
Proof. exact (EQ_MP (@lem5415794) (@lem0)). Qed.
Lemma lem5415796 : term415.
Proof. exact (@lem5415785 (@lem5415795)). Qed.
Lemma lem5415798 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415799 : term245 = term246.
Proof. exact (@lem5415798 (NUMERAL 0) term69). Qed.
Lemma lem5415800 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415801 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415802 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415801 h1) (fun h1 : term246 = True => @lem5415800)). Qed.
Lemma lem5415803 : term246 = True.
Proof. exact (EQ_MP (@lem5415802) (@lem5415800)). Qed.
Lemma lem5415804 : term245 = True.
Proof. exact (TRANS (@lem5415799) (@lem5415803)). Qed.
Lemma lem5415805 : True = term245.
Proof. exact (SYM (@lem5415804)). Qed.
Lemma lem5415806 : term245.
Proof. exact (EQ_MP (@lem5415805) (@lem0)). Qed.
Lemma lem5415807 : term413 = term416.
Proof. exact (@lem5415796 (@lem5415806)). Qed.
Lemma lem5415809 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415810 : term223 = term224.
Proof. exact (@lem5415809 term69 term69). Qed.
Lemma lem5415811 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415812 : term226 = term69.
Proof. exact (EQ_MP (@lem5415811) (@lem940073)). Qed.
Lemma lem5415813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415814 : term224 = term170.
Proof. exact (MK_COMB (@lem5415813) (@lem5415812)). Qed.
Lemma lem5415815 : term223 = term170.
Proof. exact (TRANS (@lem5415810) (@lem5415814)). Qed.
Lemma lem5415817 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415818 : term418 = term153.
Proof. exact (@lem5415817 term69). Qed.
Lemma lem5415819 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415820 : term419 = term411.
Proof. exact (MK_COMB (@lem5415819) (@lem5415818)). Qed.
Lemma lem5415821 : term416 = term245.
Proof. exact (MK_COMB (@lem5415820) (@lem5415815)). Qed.
Lemma lem5415823 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415824 : term245 = term246.
Proof. exact (@lem5415823 (NUMERAL 0) term69). Qed.
Lemma lem5415825 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415826 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415827 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415826 h1) (fun h1 : term246 = True => @lem5415825)). Qed.
Lemma lem5415828 : term246 = True.
Proof. exact (EQ_MP (@lem5415827) (@lem5415825)). Qed.
Lemma lem5415829 : term245 = True.
Proof. exact (TRANS (@lem5415824) (@lem5415828)). Qed.
Lemma lem5415830 : term416 = True.
Proof. exact (TRANS (@lem5415821) (@lem5415829)). Qed.
Lemma lem5415831 : term413 = True.
Proof. exact (TRANS (@lem5415807) (@lem5415830)). Qed.
Lemma lem5415832 : term245 = True.
Proof. exact (TRANS (@lem5415784) (@lem5415831)). Qed.
Lemma lem5415833 : term410 = True.
Proof. exact (TRANS (@lem5415775) (@lem5415832)). Qed.
Lemma lem5415834 : True = term410.
Proof. exact (SYM (@lem5415833)). Qed.
Lemma lem5415835 : term410.
Proof. exact (EQ_MP (@lem5415834) (@lem0)). Qed.
Lemma lem5415836 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term420 _69910 _69911.
Proof. exact (conj (@lem5415835) (@lem5415771 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415838 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5415839 (_69910 : int) (_69911 : int) : term422 _69910 _69911.
Proof. exact (@lem5415838 term170 (term317 _69910 _69911)). Qed.
Lemma lem5415840 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term423 _69910 _69911.
Proof. exact (@lem5415839 _69910 _69911 (@lem5415836 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415841 (_69910 : int) (_69911 : int) : (term424 _69910 _69911) = (term317 _69910 _69911).
Proof. exact (@lem1982733 (term317 _69910 _69911)). Qed.
Lemma lem5415842 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415843 (_69910 : int) (_69911 : int) : (term425 _69910 _69911) = (term322 _69910 _69911).
Proof. exact (MK_COMB (@lem5415842) (@lem5415841 _69910 _69911)). Qed.
Lemma lem5415844 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415845 (_69910 : int) (_69911 : int) : (term423 _69910 _69911) = (term323 _69910 _69911).
Proof. exact (MK_COMB (@lem5415843 _69910 _69911) (@lem5415844)). Qed.
Lemma lem5415846 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term323 _69910 _69911.
Proof. exact (EQ_MP (@lem5415845 _69910 _69911) (@lem5415840 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415848 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5415849 : term410 = term245.
Proof. exact (@lem5415848 term153 term170). Qed.
Lemma lem5415851 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415852 : term170 = term237.
Proof. exact (@lem5415851 term69). Qed.
Lemma lem5415854 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415855 : term153 = term211.
Proof. exact (@lem5415854 (NUMERAL 0)). Qed.
Lemma lem5415856 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415857 : term411 = term412.
Proof. exact (MK_COMB (@lem5415856) (@lem5415855)). Qed.
Lemma lem5415858 : term245 = term413.
Proof. exact (MK_COMB (@lem5415857) (@lem5415852)). Qed.
Lemma lem5415859 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5415861 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415862 : term245 = term246.
Proof. exact (@lem5415861 (NUMERAL 0) term69). Qed.
Lemma lem5415863 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415864 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415865 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415864 h1) (fun h1 : term246 = True => @lem5415863)). Qed.
Lemma lem5415866 : term246 = True.
Proof. exact (EQ_MP (@lem5415865) (@lem5415863)). Qed.
Lemma lem5415867 : term245 = True.
Proof. exact (TRANS (@lem5415862) (@lem5415866)). Qed.
Lemma lem5415868 : True = term245.
Proof. exact (SYM (@lem5415867)). Qed.
Lemma lem5415869 : term245.
Proof. exact (EQ_MP (@lem5415868) (@lem0)). Qed.
Lemma lem5415870 : term415.
Proof. exact (@lem5415859 (@lem5415869)). Qed.
Lemma lem5415872 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415873 : term245 = term246.
Proof. exact (@lem5415872 (NUMERAL 0) term69). Qed.
Lemma lem5415874 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415875 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415876 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415875 h1) (fun h1 : term246 = True => @lem5415874)). Qed.
Lemma lem5415877 : term246 = True.
Proof. exact (EQ_MP (@lem5415876) (@lem5415874)). Qed.
Lemma lem5415878 : term245 = True.
Proof. exact (TRANS (@lem5415873) (@lem5415877)). Qed.
Lemma lem5415879 : True = term245.
Proof. exact (SYM (@lem5415878)). Qed.
Lemma lem5415880 : term245.
Proof. exact (EQ_MP (@lem5415879) (@lem0)). Qed.
Lemma lem5415881 : term413 = term416.
Proof. exact (@lem5415870 (@lem5415880)). Qed.
Lemma lem5415883 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415884 : term223 = term224.
Proof. exact (@lem5415883 term69 term69). Qed.
Lemma lem5415885 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415886 : term226 = term69.
Proof. exact (EQ_MP (@lem5415885) (@lem940073)). Qed.
Lemma lem5415887 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415888 : term224 = term170.
Proof. exact (MK_COMB (@lem5415887) (@lem5415886)). Qed.
Lemma lem5415889 : term223 = term170.
Proof. exact (TRANS (@lem5415884) (@lem5415888)). Qed.
Lemma lem5415891 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415892 : term418 = term153.
Proof. exact (@lem5415891 term69). Qed.
Lemma lem5415893 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415894 : term419 = term411.
Proof. exact (MK_COMB (@lem5415893) (@lem5415892)). Qed.
Lemma lem5415895 : term416 = term245.
Proof. exact (MK_COMB (@lem5415894) (@lem5415889)). Qed.
Lemma lem5415897 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415898 : term245 = term246.
Proof. exact (@lem5415897 (NUMERAL 0) term69). Qed.
Lemma lem5415899 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415900 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415901 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415900 h1) (fun h1 : term246 = True => @lem5415899)). Qed.
Lemma lem5415902 : term246 = True.
Proof. exact (EQ_MP (@lem5415901) (@lem5415899)). Qed.
Lemma lem5415903 : term245 = True.
Proof. exact (TRANS (@lem5415898) (@lem5415902)). Qed.
Lemma lem5415904 : term416 = True.
Proof. exact (TRANS (@lem5415895) (@lem5415903)). Qed.
Lemma lem5415905 : term413 = True.
Proof. exact (TRANS (@lem5415881) (@lem5415904)). Qed.
Lemma lem5415906 : term245 = True.
Proof. exact (TRANS (@lem5415858) (@lem5415905)). Qed.
Lemma lem5415907 : term410 = True.
Proof. exact (TRANS (@lem5415849) (@lem5415906)). Qed.
Lemma lem5415908 : True = term410.
Proof. exact (SYM (@lem5415907)). Qed.
Lemma lem5415909 : term410.
Proof. exact (EQ_MP (@lem5415908) (@lem0)). Qed.
Lemma lem5415910 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term426 _69909 _69910.
Proof. exact (conj (@lem5415909) (@lem5415768 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415912 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5415913 (_69909 : int) (_69910 : int) : term427 _69909 _69910.
Proof. exact (@lem5415912 term170 (term289 _69909 _69910)). Qed.
Lemma lem5415914 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term428 _69909 _69910.
Proof. exact (@lem5415913 _69909 _69910 (@lem5415910 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415915 (_69909 : int) (_69910 : int) : (term429 _69909 _69910) = (term289 _69909 _69910).
Proof. exact (@lem1982733 (term289 _69909 _69910)). Qed.
Lemma lem5415916 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415917 (_69909 : int) (_69910 : int) : (term430 _69909 _69910) = (term291 _69909 _69910).
Proof. exact (MK_COMB (@lem5415916) (@lem5415915 _69909 _69910)). Qed.
Lemma lem5415918 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415919 (_69909 : int) (_69910 : int) : (term428 _69909 _69910) = (term292 _69909 _69910).
Proof. exact (MK_COMB (@lem5415917 _69909 _69910) (@lem5415918)). Qed.
Lemma lem5415920 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term292 _69909 _69910.
Proof. exact (EQ_MP (@lem5415919 _69909 _69910) (@lem5415914 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415922 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5415923 : term410 = term245.
Proof. exact (@lem5415922 term153 term170). Qed.
Lemma lem5415925 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415926 : term170 = term237.
Proof. exact (@lem5415925 term69). Qed.
Lemma lem5415928 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5415929 : term153 = term211.
Proof. exact (@lem5415928 (NUMERAL 0)). Qed.
Lemma lem5415930 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415931 : term411 = term412.
Proof. exact (MK_COMB (@lem5415930) (@lem5415929)). Qed.
Lemma lem5415932 : term245 = term413.
Proof. exact (MK_COMB (@lem5415931) (@lem5415926)). Qed.
Lemma lem5415933 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5415935 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415936 : term245 = term246.
Proof. exact (@lem5415935 (NUMERAL 0) term69). Qed.
Lemma lem5415937 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415938 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415939 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415938 h1) (fun h1 : term246 = True => @lem5415937)). Qed.
Lemma lem5415940 : term246 = True.
Proof. exact (EQ_MP (@lem5415939) (@lem5415937)). Qed.
Lemma lem5415941 : term245 = True.
Proof. exact (TRANS (@lem5415936) (@lem5415940)). Qed.
Lemma lem5415942 : True = term245.
Proof. exact (SYM (@lem5415941)). Qed.
Lemma lem5415943 : term245.
Proof. exact (EQ_MP (@lem5415942) (@lem0)). Qed.
Lemma lem5415944 : term415.
Proof. exact (@lem5415933 (@lem5415943)). Qed.
Lemma lem5415946 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415947 : term245 = term246.
Proof. exact (@lem5415946 (NUMERAL 0) term69). Qed.
Lemma lem5415948 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415949 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415950 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415949 h1) (fun h1 : term246 = True => @lem5415948)). Qed.
Lemma lem5415951 : term246 = True.
Proof. exact (EQ_MP (@lem5415950) (@lem5415948)). Qed.
Lemma lem5415952 : term245 = True.
Proof. exact (TRANS (@lem5415947) (@lem5415951)). Qed.
Lemma lem5415953 : True = term245.
Proof. exact (SYM (@lem5415952)). Qed.
Lemma lem5415954 : term245.
Proof. exact (EQ_MP (@lem5415953) (@lem0)). Qed.
Lemma lem5415955 : term413 = term416.
Proof. exact (@lem5415944 (@lem5415954)). Qed.
Lemma lem5415957 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5415958 : term223 = term224.
Proof. exact (@lem5415957 term69 term69). Qed.
Lemma lem5415959 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5415960 : term226 = term69.
Proof. exact (EQ_MP (@lem5415959) (@lem940073)). Qed.
Lemma lem5415961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5415962 : term224 = term170.
Proof. exact (MK_COMB (@lem5415961) (@lem5415960)). Qed.
Lemma lem5415963 : term223 = term170.
Proof. exact (TRANS (@lem5415958) (@lem5415962)). Qed.
Lemma lem5415965 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5415966 : term418 = term153.
Proof. exact (@lem5415965 term69). Qed.
Lemma lem5415967 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5415968 : term419 = term411.
Proof. exact (MK_COMB (@lem5415967) (@lem5415966)). Qed.
Lemma lem5415969 : term416 = term245.
Proof. exact (MK_COMB (@lem5415968) (@lem5415963)). Qed.
Lemma lem5415971 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5415972 : term245 = term246.
Proof. exact (@lem5415971 (NUMERAL 0) term69). Qed.
Lemma lem5415973 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5415974 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5415975 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5415974 h1) (fun h1 : term246 = True => @lem5415973)). Qed.
Lemma lem5415976 : term246 = True.
Proof. exact (EQ_MP (@lem5415975) (@lem5415973)). Qed.
Lemma lem5415977 : term245 = True.
Proof. exact (TRANS (@lem5415972) (@lem5415976)). Qed.
Lemma lem5415978 : term416 = True.
Proof. exact (TRANS (@lem5415969) (@lem5415977)). Qed.
Lemma lem5415979 : term413 = True.
Proof. exact (TRANS (@lem5415955) (@lem5415978)). Qed.
Lemma lem5415980 : term245 = True.
Proof. exact (TRANS (@lem5415932) (@lem5415979)). Qed.
Lemma lem5415981 : term410 = True.
Proof. exact (TRANS (@lem5415923) (@lem5415980)). Qed.
Lemma lem5415982 : True = term410.
Proof. exact (SYM (@lem5415981)). Qed.
Lemma lem5415983 : term410.
Proof. exact (EQ_MP (@lem5415982) (@lem0)). Qed.
Lemma lem5415984 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term463 _69909 _69911.
Proof. exact (conj (@lem5415983) (@lem5415772 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415986 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5415987 (_69909 : int) (_69911 : int) : term464 _69909 _69911.
Proof. exact (@lem5415986 term170 (term318 _69909 _69911)). Qed.
Lemma lem5415988 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term465 _69909 _69911.
Proof. exact (@lem5415987 _69909 _69911 (@lem5415984 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415989 (_69909 : int) (_69911 : int) : (term466 _69909 _69911) = (term318 _69909 _69911).
Proof. exact (@lem1982733 (term318 _69909 _69911)). Qed.
Lemma lem5415990 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5415991 (_69909 : int) (_69911 : int) : (term467 _69909 _69911) = (term320 _69909 _69911).
Proof. exact (MK_COMB (@lem5415990) (@lem5415989 _69909 _69911)). Qed.
Lemma lem5415992 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5415993 (_69909 : int) (_69911 : int) : (term465 _69909 _69911) = (term321 _69909 _69911).
Proof. exact (MK_COMB (@lem5415991 _69909 _69911) (@lem5415992)). Qed.
Lemma lem5415994 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term321 _69909 _69911.
Proof. exact (EQ_MP (@lem5415993 _69909 _69911) (@lem5415988 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415995 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term496 _69911 _69909 _69910.
Proof. exact (conj (@lem5415994 _69909 _69910 _69911 h1) (@lem5415920 _69909 _69910 _69911 h1)). Qed.
Lemma lem5415997 (x : real) (y : real) : term432 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5415998 (_69911 : int) (_69909 : int) (_69910 : int) : term497 _69911 _69909 _69910.
Proof. exact (@lem5415997 (term318 _69909 _69911) (term289 _69909 _69910)). Qed.
Lemma lem5415999 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term498 _69911 _69909 _69910.
Proof. exact (@lem5415998 _69911 _69909 _69910 (@lem5415995 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416000 (_69909 : int) (_69911 : int) (_69910 : int) : (term499 _69911 _69909 _69910) = (term500 _69909 _69911 _69910).
Proof. exact (@lem1982753 (term310 _69909) (real_of_int _69909) (real_of_int _69911) (term288 _69910)). Qed.
Lemma lem5416001 (_69909 : int) : (term439 _69909) = (term440 _69909).
Proof. exact (@lem1982713 term214 (real_of_int _69909)). Qed.
Lemma lem5416003 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416004 : term170 = term237.
Proof. exact (@lem5416003 term69). Qed.
Lemma lem5416006 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5416007 : term214 = term215.
Proof. exact (@lem5416006 term69). Qed.
Lemma lem5416008 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416009 : term441 = term442.
Proof. exact (MK_COMB (@lem5416008) (@lem5416007)). Qed.
Lemma lem5416010 : term443 = term444.
Proof. exact (MK_COMB (@lem5416009) (@lem5416004)). Qed.
Lemma lem5416011 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5416013 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416014 : term245 = term246.
Proof. exact (@lem5416013 (NUMERAL 0) term69). Qed.
Lemma lem5416015 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416016 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416017 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416016 h1) (fun h1 : term246 = True => @lem5416015)). Qed.
Lemma lem5416018 : term246 = True.
Proof. exact (EQ_MP (@lem5416017) (@lem5416015)). Qed.
Lemma lem5416019 : term245 = True.
Proof. exact (TRANS (@lem5416014) (@lem5416018)). Qed.
Lemma lem5416020 : True = term245.
Proof. exact (SYM (@lem5416019)). Qed.
Lemma lem5416021 : term245.
Proof. exact (EQ_MP (@lem5416020) (@lem0)). Qed.
Lemma lem5416022 : term446.
Proof. exact (@lem5416011 (@lem5416021)). Qed.
Lemma lem5416024 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416025 : term245 = term246.
Proof. exact (@lem5416024 (NUMERAL 0) term69). Qed.
Lemma lem5416026 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416027 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416028 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416027 h1) (fun h1 : term246 = True => @lem5416026)). Qed.
Lemma lem5416029 : term246 = True.
Proof. exact (EQ_MP (@lem5416028) (@lem5416026)). Qed.
Lemma lem5416030 : term245 = True.
Proof. exact (TRANS (@lem5416025) (@lem5416029)). Qed.
Lemma lem5416031 : True = term245.
Proof. exact (SYM (@lem5416030)). Qed.
Lemma lem5416032 : term245.
Proof. exact (EQ_MP (@lem5416031) (@lem0)). Qed.
Lemma lem5416033 : term447.
Proof. exact (@lem5416022 (@lem5416032)). Qed.
Lemma lem5416035 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416036 : term245 = term246.
Proof. exact (@lem5416035 (NUMERAL 0) term69). Qed.
Lemma lem5416037 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416038 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416039 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416038 h1) (fun h1 : term246 = True => @lem5416037)). Qed.
Lemma lem5416040 : term246 = True.
Proof. exact (EQ_MP (@lem5416039) (@lem5416037)). Qed.
Lemma lem5416041 : term245 = True.
Proof. exact (TRANS (@lem5416036) (@lem5416040)). Qed.
Lemma lem5416042 : True = term245.
Proof. exact (SYM (@lem5416041)). Qed.
Lemma lem5416043 : term245.
Proof. exact (EQ_MP (@lem5416042) (@lem0)). Qed.
Lemma lem5416044 : term448.
Proof. exact (@lem5416033 (@lem5416043)). Qed.
Lemma lem5416046 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416047 : term223 = term224.
Proof. exact (@lem5416046 term69 term69). Qed.
Lemma lem5416048 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416049 : term226 = term69.
Proof. exact (EQ_MP (@lem5416048) (@lem940073)). Qed.
Lemma lem5416050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416051 : term224 = term170.
Proof. exact (MK_COMB (@lem5416050) (@lem5416049)). Qed.
Lemma lem5416052 : term223 = term170.
Proof. exact (TRANS (@lem5416047) (@lem5416051)). Qed.
Lemma lem5416054 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5416055 : term298 = term301.
Proof. exact (@lem5416054 term69 term69). Qed.
Lemma lem5416056 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416057 : term226 = term69.
Proof. exact (EQ_MP (@lem5416056) (@lem940073)). Qed.
Lemma lem5416058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416059 : term224 = term170.
Proof. exact (MK_COMB (@lem5416058) (@lem5416057)). Qed.
Lemma lem5416060 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416061 : term301 = term214.
Proof. exact (MK_COMB (@lem5416060) (@lem5416059)). Qed.
Lemma lem5416062 : term298 = term214.
Proof. exact (TRANS (@lem5416055) (@lem5416061)). Qed.
Lemma lem5416063 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416064 : term449 = term441.
Proof. exact (MK_COMB (@lem5416063) (@lem5416062)). Qed.
Lemma lem5416065 : term450 = term443.
Proof. exact (MK_COMB (@lem5416064) (@lem5416052)). Qed.
Lemma lem5416067 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5416068 : term443 = term153.
Proof. exact (@lem5416067 term69). Qed.
Lemma lem5416069 : term450 = term153.
Proof. exact (TRANS (@lem5416065) (@lem5416068)). Qed.
Lemma lem5416070 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416071 : term452 = term453.
Proof. exact (MK_COMB (@lem5416070) (@lem5416069)). Qed.
Lemma lem5416072 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5416073 : term454 = term418.
Proof. exact (MK_COMB (@lem5416071) (@lem5416072)). Qed.
Lemma lem5416075 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416076 : term418 = term153.
Proof. exact (@lem5416075 term69). Qed.
Lemma lem5416077 : term454 = term153.
Proof. exact (TRANS (@lem5416073) (@lem5416076)). Qed.
Lemma lem5416079 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416080 : term223 = term224.
Proof. exact (@lem5416079 term69 term69). Qed.
Lemma lem5416081 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416082 : term226 = term69.
Proof. exact (EQ_MP (@lem5416081) (@lem940073)). Qed.
Lemma lem5416083 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416084 : term224 = term170.
Proof. exact (MK_COMB (@lem5416083) (@lem5416082)). Qed.
Lemma lem5416085 : term223 = term170.
Proof. exact (TRANS (@lem5416080) (@lem5416084)). Qed.
Lemma lem5416086 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5416087 : term455 = term418.
Proof. exact (MK_COMB (@lem5416086) (@lem5416085)). Qed.
Lemma lem5416089 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416090 : term418 = term153.
Proof. exact (@lem5416089 term69). Qed.
Lemma lem5416091 : term455 = term153.
Proof. exact (TRANS (@lem5416087) (@lem5416090)). Qed.
Lemma lem5416092 : term153 = term455.
Proof. exact (SYM (@lem5416091)). Qed.
Lemma lem5416093 : term454 = term455.
Proof. exact (TRANS (@lem5416077) (@lem5416092)). Qed.
Lemma lem5416094 : term444 = term211.
Proof. exact (@lem5416044 (@lem5416093)). Qed.
Lemma lem5416095 : term443 = term211.
Proof. exact (TRANS (@lem5416010) (@lem5416094)). Qed.
Lemma lem5416097 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5416098 : term211 = term153.
Proof. exact (@lem5416097 term153). Qed.
Lemma lem5416099 : term443 = term153.
Proof. exact (TRANS (@lem5416095) (@lem5416098)). Qed.
Lemma lem5416100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416101 : term456 = term453.
Proof. exact (MK_COMB (@lem5416100) (@lem5416099)). Qed.
Lemma lem5416102 (_69909 : int) : (real_of_int _69909) = (real_of_int _69909).
Proof. exact (eq_refl (real_of_int _69909)). Qed.
Lemma lem5416103 (_69909 : int) : (term440 _69909) = (term457 _69909).
Proof. exact (MK_COMB (@lem5416101) (@lem5416102 _69909)). Qed.
Lemma lem5416104 (_69909 : int) : (term439 _69909) = (term457 _69909).
Proof. exact (TRANS (@lem5416001 _69909) (@lem5416103 _69909)). Qed.
Lemma lem5416105 (_69909 : int) : (term457 _69909) = term153.
Proof. exact (@lem1982719 (real_of_int _69909)). Qed.
Lemma lem5416106 (_69909 : int) : (term439 _69909) = term153.
Proof. exact (TRANS (@lem5416104 _69909) (@lem5416105 _69909)). Qed.
Lemma lem5416107 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416108 (_69909 : int) : (term458 _69909) = term459.
Proof. exact (MK_COMB (@lem5416107) (@lem5416106 _69909)). Qed.
Lemma lem5416113 (_69910 : int) (_69911 : int) : (term289 _69911 _69910) = (term309 _69910 _69911).
Proof. exact (@lem1982757 (term310 _69910) (real_of_int _69911) term283). Qed.
Lemma lem5416114 (_69909 : int) (_69910 : int) (_69911 : int) : (term500 _69909 _69911 _69910) = (term501 _69910 _69911).
Proof. exact (MK_COMB (@lem5416108 _69909) (@lem5416113 _69910 _69911)). Qed.
Lemma lem5416115 (_69909 : int) (_69910 : int) (_69911 : int) : (term499 _69911 _69909 _69910) = (term501 _69910 _69911).
Proof. exact (TRANS (@lem5416000 _69909 _69911 _69910) (@lem5416114 _69909 _69910 _69911)). Qed.
Lemma lem5416116 (_69910 : int) (_69911 : int) : (term501 _69910 _69911) = (term309 _69910 _69911).
Proof. exact (@lem1982721 (term309 _69910 _69911)). Qed.
Lemma lem5416117 (_69909 : int) (_69910 : int) (_69911 : int) : (term499 _69911 _69909 _69910) = (term309 _69910 _69911).
Proof. exact (TRANS (@lem5416115 _69909 _69910 _69911) (@lem5416116 _69910 _69911)). Qed.
Lemma lem5416118 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5416119 (_69909 : int) (_69910 : int) (_69911 : int) : (term502 _69911 _69909 _69910) = (term311 _69910 _69911).
Proof. exact (MK_COMB (@lem5416118) (@lem5416117 _69909 _69910 _69911)). Qed.
Lemma lem5416120 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5416121 (_69909 : int) (_69910 : int) (_69911 : int) : (term498 _69911 _69909 _69910) = (term312 _69910 _69911).
Proof. exact (MK_COMB (@lem5416119 _69909 _69910 _69911) (@lem5416120)). Qed.
Lemma lem5416122 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term312 _69910 _69911.
Proof. exact (EQ_MP (@lem5416121 _69909 _69910 _69911) (@lem5415999 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416124 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5416125 : term410 = term245.
Proof. exact (@lem5416124 term153 term170). Qed.
Lemma lem5416127 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416128 : term170 = term237.
Proof. exact (@lem5416127 term69). Qed.
Lemma lem5416130 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416131 : term153 = term211.
Proof. exact (@lem5416130 (NUMERAL 0)). Qed.
Lemma lem5416132 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5416133 : term411 = term412.
Proof. exact (MK_COMB (@lem5416132) (@lem5416131)). Qed.
Lemma lem5416134 : term245 = term413.
Proof. exact (MK_COMB (@lem5416133) (@lem5416128)). Qed.
Lemma lem5416135 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5416137 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416138 : term245 = term246.
Proof. exact (@lem5416137 (NUMERAL 0) term69). Qed.
Lemma lem5416139 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416140 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416141 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416140 h1) (fun h1 : term246 = True => @lem5416139)). Qed.
Lemma lem5416142 : term246 = True.
Proof. exact (EQ_MP (@lem5416141) (@lem5416139)). Qed.
Lemma lem5416143 : term245 = True.
Proof. exact (TRANS (@lem5416138) (@lem5416142)). Qed.
Lemma lem5416144 : True = term245.
Proof. exact (SYM (@lem5416143)). Qed.
Lemma lem5416145 : term245.
Proof. exact (EQ_MP (@lem5416144) (@lem0)). Qed.
Lemma lem5416146 : term415.
Proof. exact (@lem5416135 (@lem5416145)). Qed.
Lemma lem5416148 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416149 : term245 = term246.
Proof. exact (@lem5416148 (NUMERAL 0) term69). Qed.
Lemma lem5416150 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416151 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416152 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416151 h1) (fun h1 : term246 = True => @lem5416150)). Qed.
Lemma lem5416153 : term246 = True.
Proof. exact (EQ_MP (@lem5416152) (@lem5416150)). Qed.
Lemma lem5416154 : term245 = True.
Proof. exact (TRANS (@lem5416149) (@lem5416153)). Qed.
Lemma lem5416155 : True = term245.
Proof. exact (SYM (@lem5416154)). Qed.
Lemma lem5416156 : term245.
Proof. exact (EQ_MP (@lem5416155) (@lem0)). Qed.
Lemma lem5416157 : term413 = term416.
Proof. exact (@lem5416146 (@lem5416156)). Qed.
Lemma lem5416159 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416160 : term223 = term224.
Proof. exact (@lem5416159 term69 term69). Qed.
Lemma lem5416161 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416162 : term226 = term69.
Proof. exact (EQ_MP (@lem5416161) (@lem940073)). Qed.
Lemma lem5416163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416164 : term224 = term170.
Proof. exact (MK_COMB (@lem5416163) (@lem5416162)). Qed.
Lemma lem5416165 : term223 = term170.
Proof. exact (TRANS (@lem5416160) (@lem5416164)). Qed.
Lemma lem5416167 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416168 : term418 = term153.
Proof. exact (@lem5416167 term69). Qed.
Lemma lem5416169 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5416170 : term419 = term411.
Proof. exact (MK_COMB (@lem5416169) (@lem5416168)). Qed.
Lemma lem5416171 : term416 = term245.
Proof. exact (MK_COMB (@lem5416170) (@lem5416165)). Qed.
Lemma lem5416173 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416174 : term245 = term246.
Proof. exact (@lem5416173 (NUMERAL 0) term69). Qed.
Lemma lem5416175 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416176 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416177 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416176 h1) (fun h1 : term246 = True => @lem5416175)). Qed.
Lemma lem5416178 : term246 = True.
Proof. exact (EQ_MP (@lem5416177) (@lem5416175)). Qed.
Lemma lem5416179 : term245 = True.
Proof. exact (TRANS (@lem5416174) (@lem5416178)). Qed.
Lemma lem5416180 : term416 = True.
Proof. exact (TRANS (@lem5416171) (@lem5416179)). Qed.
Lemma lem5416181 : term413 = True.
Proof. exact (TRANS (@lem5416157) (@lem5416180)). Qed.
Lemma lem5416182 : term245 = True.
Proof. exact (TRANS (@lem5416134) (@lem5416181)). Qed.
Lemma lem5416183 : term410 = True.
Proof. exact (TRANS (@lem5416125) (@lem5416182)). Qed.
Lemma lem5416184 : True = term410.
Proof. exact (SYM (@lem5416183)). Qed.
Lemma lem5416185 : term410.
Proof. exact (EQ_MP (@lem5416184) (@lem0)). Qed.
Lemma lem5416186 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term503 _69910 _69911.
Proof. exact (conj (@lem5416185) (@lem5416122 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416188 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5416189 (_69910 : int) (_69911 : int) : term504 _69910 _69911.
Proof. exact (@lem5416188 term170 (term309 _69910 _69911)). Qed.
Lemma lem5416190 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term505 _69910 _69911.
Proof. exact (@lem5416189 _69910 _69911 (@lem5416186 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416191 (_69910 : int) (_69911 : int) : (term506 _69910 _69911) = (term309 _69910 _69911).
Proof. exact (@lem1982733 (term309 _69910 _69911)). Qed.
Lemma lem5416192 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5416193 (_69910 : int) (_69911 : int) : (term507 _69910 _69911) = (term311 _69910 _69911).
Proof. exact (MK_COMB (@lem5416192) (@lem5416191 _69910 _69911)). Qed.
Lemma lem5416194 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5416195 (_69910 : int) (_69911 : int) : (term505 _69910 _69911) = (term312 _69910 _69911).
Proof. exact (MK_COMB (@lem5416193 _69910 _69911) (@lem5416194)). Qed.
Lemma lem5416196 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term312 _69910 _69911.
Proof. exact (EQ_MP (@lem5416195 _69910 _69911) (@lem5416190 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416197 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term508 _69910 _69911.
Proof. exact (conj (@lem5416196 _69909 _69910 _69911 h1) (@lem5415846 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416199 (x : real) (y : real) : term432 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5416200 (_69910 : int) (_69911 : int) : term509 _69910 _69911.
Proof. exact (@lem5416199 (term309 _69910 _69911) (term317 _69910 _69911)). Qed.
Lemma lem5416201 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term510 _69910 _69911.
Proof. exact (@lem5416200 _69910 _69911 (@lem5416197 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416202 (_69910 : int) (_69911 : int) : (term511 _69910 _69911) = (term512 _69910 _69911).
Proof. exact (@lem1982753 (term310 _69910) (real_of_int _69910) (term513 _69911) (term310 _69911)). Qed.
Lemma lem5416203 (_69910 : int) : (term439 _69910) = (term440 _69910).
Proof. exact (@lem1982713 term214 (real_of_int _69910)). Qed.
Lemma lem5416205 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416206 : term170 = term237.
Proof. exact (@lem5416205 term69). Qed.
Lemma lem5416208 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5416209 : term214 = term215.
Proof. exact (@lem5416208 term69). Qed.
Lemma lem5416210 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416211 : term441 = term442.
Proof. exact (MK_COMB (@lem5416210) (@lem5416209)). Qed.
Lemma lem5416212 : term443 = term444.
Proof. exact (MK_COMB (@lem5416211) (@lem5416206)). Qed.
Lemma lem5416213 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5416215 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416216 : term245 = term246.
Proof. exact (@lem5416215 (NUMERAL 0) term69). Qed.
Lemma lem5416217 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416218 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416219 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416218 h1) (fun h1 : term246 = True => @lem5416217)). Qed.
Lemma lem5416220 : term246 = True.
Proof. exact (EQ_MP (@lem5416219) (@lem5416217)). Qed.
Lemma lem5416221 : term245 = True.
Proof. exact (TRANS (@lem5416216) (@lem5416220)). Qed.
Lemma lem5416222 : True = term245.
Proof. exact (SYM (@lem5416221)). Qed.
Lemma lem5416223 : term245.
Proof. exact (EQ_MP (@lem5416222) (@lem0)). Qed.
Lemma lem5416224 : term446.
Proof. exact (@lem5416213 (@lem5416223)). Qed.
Lemma lem5416226 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416227 : term245 = term246.
Proof. exact (@lem5416226 (NUMERAL 0) term69). Qed.
Lemma lem5416228 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416229 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416230 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416229 h1) (fun h1 : term246 = True => @lem5416228)). Qed.
Lemma lem5416231 : term246 = True.
Proof. exact (EQ_MP (@lem5416230) (@lem5416228)). Qed.
Lemma lem5416232 : term245 = True.
Proof. exact (TRANS (@lem5416227) (@lem5416231)). Qed.
Lemma lem5416233 : True = term245.
Proof. exact (SYM (@lem5416232)). Qed.
Lemma lem5416234 : term245.
Proof. exact (EQ_MP (@lem5416233) (@lem0)). Qed.
Lemma lem5416235 : term447.
Proof. exact (@lem5416224 (@lem5416234)). Qed.
Lemma lem5416237 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416238 : term245 = term246.
Proof. exact (@lem5416237 (NUMERAL 0) term69). Qed.
Lemma lem5416239 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416240 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416241 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416240 h1) (fun h1 : term246 = True => @lem5416239)). Qed.
Lemma lem5416242 : term246 = True.
Proof. exact (EQ_MP (@lem5416241) (@lem5416239)). Qed.
Lemma lem5416243 : term245 = True.
Proof. exact (TRANS (@lem5416238) (@lem5416242)). Qed.
Lemma lem5416244 : True = term245.
Proof. exact (SYM (@lem5416243)). Qed.
Lemma lem5416245 : term245.
Proof. exact (EQ_MP (@lem5416244) (@lem0)). Qed.
Lemma lem5416246 : term448.
Proof. exact (@lem5416235 (@lem5416245)). Qed.
Lemma lem5416248 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416249 : term223 = term224.
Proof. exact (@lem5416248 term69 term69). Qed.
Lemma lem5416250 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416251 : term226 = term69.
Proof. exact (EQ_MP (@lem5416250) (@lem940073)). Qed.
Lemma lem5416252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416253 : term224 = term170.
Proof. exact (MK_COMB (@lem5416252) (@lem5416251)). Qed.
Lemma lem5416254 : term223 = term170.
Proof. exact (TRANS (@lem5416249) (@lem5416253)). Qed.
Lemma lem5416256 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5416257 : term298 = term301.
Proof. exact (@lem5416256 term69 term69). Qed.
Lemma lem5416258 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416259 : term226 = term69.
Proof. exact (EQ_MP (@lem5416258) (@lem940073)). Qed.
Lemma lem5416260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416261 : term224 = term170.
Proof. exact (MK_COMB (@lem5416260) (@lem5416259)). Qed.
Lemma lem5416262 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416263 : term301 = term214.
Proof. exact (MK_COMB (@lem5416262) (@lem5416261)). Qed.
Lemma lem5416264 : term298 = term214.
Proof. exact (TRANS (@lem5416257) (@lem5416263)). Qed.
Lemma lem5416265 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416266 : term449 = term441.
Proof. exact (MK_COMB (@lem5416265) (@lem5416264)). Qed.
Lemma lem5416267 : term450 = term443.
Proof. exact (MK_COMB (@lem5416266) (@lem5416254)). Qed.
Lemma lem5416269 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5416270 : term443 = term153.
Proof. exact (@lem5416269 term69). Qed.
Lemma lem5416271 : term450 = term153.
Proof. exact (TRANS (@lem5416267) (@lem5416270)). Qed.
Lemma lem5416272 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416273 : term452 = term453.
Proof. exact (MK_COMB (@lem5416272) (@lem5416271)). Qed.
Lemma lem5416274 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5416275 : term454 = term418.
Proof. exact (MK_COMB (@lem5416273) (@lem5416274)). Qed.
Lemma lem5416277 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416278 : term418 = term153.
Proof. exact (@lem5416277 term69). Qed.
Lemma lem5416279 : term454 = term153.
Proof. exact (TRANS (@lem5416275) (@lem5416278)). Qed.
Lemma lem5416281 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416282 : term223 = term224.
Proof. exact (@lem5416281 term69 term69). Qed.
Lemma lem5416283 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416284 : term226 = term69.
Proof. exact (EQ_MP (@lem5416283) (@lem940073)). Qed.
Lemma lem5416285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416286 : term224 = term170.
Proof. exact (MK_COMB (@lem5416285) (@lem5416284)). Qed.
Lemma lem5416287 : term223 = term170.
Proof. exact (TRANS (@lem5416282) (@lem5416286)). Qed.
Lemma lem5416288 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5416289 : term455 = term418.
Proof. exact (MK_COMB (@lem5416288) (@lem5416287)). Qed.
Lemma lem5416291 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416292 : term418 = term153.
Proof. exact (@lem5416291 term69). Qed.
Lemma lem5416293 : term455 = term153.
Proof. exact (TRANS (@lem5416289) (@lem5416292)). Qed.
Lemma lem5416294 : term153 = term455.
Proof. exact (SYM (@lem5416293)). Qed.
Lemma lem5416295 : term454 = term455.
Proof. exact (TRANS (@lem5416279) (@lem5416294)). Qed.
Lemma lem5416296 : term444 = term211.
Proof. exact (@lem5416246 (@lem5416295)). Qed.
Lemma lem5416297 : term443 = term211.
Proof. exact (TRANS (@lem5416212) (@lem5416296)). Qed.
Lemma lem5416299 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5416300 : term211 = term153.
Proof. exact (@lem5416299 term153). Qed.
Lemma lem5416301 : term443 = term153.
Proof. exact (TRANS (@lem5416297) (@lem5416300)). Qed.
Lemma lem5416302 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416303 : term456 = term453.
Proof. exact (MK_COMB (@lem5416302) (@lem5416301)). Qed.
Lemma lem5416304 (_69910 : int) : (real_of_int _69910) = (real_of_int _69910).
Proof. exact (eq_refl (real_of_int _69910)). Qed.
Lemma lem5416305 (_69910 : int) : (term440 _69910) = (term457 _69910).
Proof. exact (MK_COMB (@lem5416303) (@lem5416304 _69910)). Qed.
Lemma lem5416306 (_69910 : int) : (term439 _69910) = (term457 _69910).
Proof. exact (TRANS (@lem5416203 _69910) (@lem5416305 _69910)). Qed.
Lemma lem5416307 (_69910 : int) : (term457 _69910) = term153.
Proof. exact (@lem1982719 (real_of_int _69910)). Qed.
Lemma lem5416308 (_69910 : int) : (term439 _69910) = term153.
Proof. exact (TRANS (@lem5416306 _69910) (@lem5416307 _69910)). Qed.
Lemma lem5416309 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416310 (_69910 : int) : (term458 _69910) = term459.
Proof. exact (MK_COMB (@lem5416309) (@lem5416308 _69910)). Qed.
Lemma lem5416311 (_69911 : int) : (term514 _69911) = (term474 _69911).
Proof. exact (@lem1982759 (real_of_int _69911) (term310 _69911) term283). Qed.
Lemma lem5416312 (_69911 : int) : (term475 _69911) = (term440 _69911).
Proof. exact (@lem1982715 term214 (real_of_int _69911)). Qed.
Lemma lem5416314 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416315 : term170 = term237.
Proof. exact (@lem5416314 term69). Qed.
Lemma lem5416317 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5416318 : term214 = term215.
Proof. exact (@lem5416317 term69). Qed.
Lemma lem5416319 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416320 : term441 = term442.
Proof. exact (MK_COMB (@lem5416319) (@lem5416318)). Qed.
Lemma lem5416321 : term443 = term444.
Proof. exact (MK_COMB (@lem5416320) (@lem5416315)). Qed.
Lemma lem5416322 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5416324 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416325 : term245 = term246.
Proof. exact (@lem5416324 (NUMERAL 0) term69). Qed.
Lemma lem5416326 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416327 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416328 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416327 h1) (fun h1 : term246 = True => @lem5416326)). Qed.
Lemma lem5416329 : term246 = True.
Proof. exact (EQ_MP (@lem5416328) (@lem5416326)). Qed.
Lemma lem5416330 : term245 = True.
Proof. exact (TRANS (@lem5416325) (@lem5416329)). Qed.
Lemma lem5416331 : True = term245.
Proof. exact (SYM (@lem5416330)). Qed.
Lemma lem5416332 : term245.
Proof. exact (EQ_MP (@lem5416331) (@lem0)). Qed.
Lemma lem5416333 : term446.
Proof. exact (@lem5416322 (@lem5416332)). Qed.
Lemma lem5416335 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416336 : term245 = term246.
Proof. exact (@lem5416335 (NUMERAL 0) term69). Qed.
Lemma lem5416337 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416338 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416339 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416338 h1) (fun h1 : term246 = True => @lem5416337)). Qed.
Lemma lem5416340 : term246 = True.
Proof. exact (EQ_MP (@lem5416339) (@lem5416337)). Qed.
Lemma lem5416341 : term245 = True.
Proof. exact (TRANS (@lem5416336) (@lem5416340)). Qed.
Lemma lem5416342 : True = term245.
Proof. exact (SYM (@lem5416341)). Qed.
Lemma lem5416343 : term245.
Proof. exact (EQ_MP (@lem5416342) (@lem0)). Qed.
Lemma lem5416344 : term447.
Proof. exact (@lem5416333 (@lem5416343)). Qed.
Lemma lem5416346 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416347 : term245 = term246.
Proof. exact (@lem5416346 (NUMERAL 0) term69). Qed.
Lemma lem5416348 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416349 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416350 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416349 h1) (fun h1 : term246 = True => @lem5416348)). Qed.
Lemma lem5416351 : term246 = True.
Proof. exact (EQ_MP (@lem5416350) (@lem5416348)). Qed.
Lemma lem5416352 : term245 = True.
Proof. exact (TRANS (@lem5416347) (@lem5416351)). Qed.
Lemma lem5416353 : True = term245.
Proof. exact (SYM (@lem5416352)). Qed.
Lemma lem5416354 : term245.
Proof. exact (EQ_MP (@lem5416353) (@lem0)). Qed.
Lemma lem5416355 : term448.
Proof. exact (@lem5416344 (@lem5416354)). Qed.
Lemma lem5416357 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416358 : term223 = term224.
Proof. exact (@lem5416357 term69 term69). Qed.
Lemma lem5416359 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416360 : term226 = term69.
Proof. exact (EQ_MP (@lem5416359) (@lem940073)). Qed.
Lemma lem5416361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416362 : term224 = term170.
Proof. exact (MK_COMB (@lem5416361) (@lem5416360)). Qed.
Lemma lem5416363 : term223 = term170.
Proof. exact (TRANS (@lem5416358) (@lem5416362)). Qed.
Lemma lem5416365 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5416366 : term298 = term301.
Proof. exact (@lem5416365 term69 term69). Qed.
Lemma lem5416367 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416368 : term226 = term69.
Proof. exact (EQ_MP (@lem5416367) (@lem940073)). Qed.
Lemma lem5416369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416370 : term224 = term170.
Proof. exact (MK_COMB (@lem5416369) (@lem5416368)). Qed.
Lemma lem5416371 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416372 : term301 = term214.
Proof. exact (MK_COMB (@lem5416371) (@lem5416370)). Qed.
Lemma lem5416373 : term298 = term214.
Proof. exact (TRANS (@lem5416366) (@lem5416372)). Qed.
Lemma lem5416374 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416375 : term449 = term441.
Proof. exact (MK_COMB (@lem5416374) (@lem5416373)). Qed.
Lemma lem5416376 : term450 = term443.
Proof. exact (MK_COMB (@lem5416375) (@lem5416363)). Qed.
Lemma lem5416378 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5416379 : term443 = term153.
Proof. exact (@lem5416378 term69). Qed.
Lemma lem5416380 : term450 = term153.
Proof. exact (TRANS (@lem5416376) (@lem5416379)). Qed.
Lemma lem5416381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416382 : term452 = term453.
Proof. exact (MK_COMB (@lem5416381) (@lem5416380)). Qed.
Lemma lem5416383 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5416384 : term454 = term418.
Proof. exact (MK_COMB (@lem5416382) (@lem5416383)). Qed.
Lemma lem5416386 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416387 : term418 = term153.
Proof. exact (@lem5416386 term69). Qed.
Lemma lem5416388 : term454 = term153.
Proof. exact (TRANS (@lem5416384) (@lem5416387)). Qed.
Lemma lem5416390 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416391 : term223 = term224.
Proof. exact (@lem5416390 term69 term69). Qed.
Lemma lem5416392 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416393 : term226 = term69.
Proof. exact (EQ_MP (@lem5416392) (@lem940073)). Qed.
Lemma lem5416394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416395 : term224 = term170.
Proof. exact (MK_COMB (@lem5416394) (@lem5416393)). Qed.
Lemma lem5416396 : term223 = term170.
Proof. exact (TRANS (@lem5416391) (@lem5416395)). Qed.
Lemma lem5416397 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5416398 : term455 = term418.
Proof. exact (MK_COMB (@lem5416397) (@lem5416396)). Qed.
Lemma lem5416400 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416401 : term418 = term153.
Proof. exact (@lem5416400 term69). Qed.
Lemma lem5416402 : term455 = term153.
Proof. exact (TRANS (@lem5416398) (@lem5416401)). Qed.
Lemma lem5416403 : term153 = term455.
Proof. exact (SYM (@lem5416402)). Qed.
Lemma lem5416404 : term454 = term455.
Proof. exact (TRANS (@lem5416388) (@lem5416403)). Qed.
Lemma lem5416405 : term444 = term211.
Proof. exact (@lem5416355 (@lem5416404)). Qed.
Lemma lem5416406 : term443 = term211.
Proof. exact (TRANS (@lem5416321) (@lem5416405)). Qed.
Lemma lem5416408 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5416409 : term211 = term153.
Proof. exact (@lem5416408 term153). Qed.
Lemma lem5416410 : term443 = term153.
Proof. exact (TRANS (@lem5416406) (@lem5416409)). Qed.
Lemma lem5416411 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416412 : term456 = term453.
Proof. exact (MK_COMB (@lem5416411) (@lem5416410)). Qed.
Lemma lem5416413 (_69911 : int) : (real_of_int _69911) = (real_of_int _69911).
Proof. exact (eq_refl (real_of_int _69911)). Qed.
Lemma lem5416414 (_69911 : int) : (term440 _69911) = (term457 _69911).
Proof. exact (MK_COMB (@lem5416412) (@lem5416413 _69911)). Qed.
Lemma lem5416415 (_69911 : int) : (term475 _69911) = (term457 _69911).
Proof. exact (TRANS (@lem5416312 _69911) (@lem5416414 _69911)). Qed.
Lemma lem5416416 (_69911 : int) : (term457 _69911) = term153.
Proof. exact (@lem1982719 (real_of_int _69911)). Qed.
Lemma lem5416417 (_69911 : int) : (term475 _69911) = term153.
Proof. exact (TRANS (@lem5416415 _69911) (@lem5416416 _69911)). Qed.
Lemma lem5416418 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416419 (_69911 : int) : (term476 _69911) = term459.
Proof. exact (MK_COMB (@lem5416418) (@lem5416417 _69911)). Qed.
Lemma lem5416420 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem5416421 (_69911 : int) : (term474 _69911) = term477.
Proof. exact (MK_COMB (@lem5416419 _69911) (@lem5416420)). Qed.
Lemma lem5416422 (_69911 : int) : (term514 _69911) = term477.
Proof. exact (TRANS (@lem5416311 _69911) (@lem5416421 _69911)). Qed.
Lemma lem5416423 : term477 = term283.
Proof. exact (@lem1982721 term283). Qed.
Lemma lem5416424 (_69911 : int) : (term514 _69911) = term283.
Proof. exact (TRANS (@lem5416422 _69911) (@lem5416423)). Qed.
Lemma lem5416425 (_69910 : int) (_69911 : int) : (term512 _69910 _69911) = term477.
Proof. exact (MK_COMB (@lem5416310 _69910) (@lem5416424 _69911)). Qed.
Lemma lem5416426 (_69910 : int) (_69911 : int) : (term511 _69910 _69911) = term477.
Proof. exact (TRANS (@lem5416202 _69910 _69911) (@lem5416425 _69910 _69911)). Qed.
Lemma lem5416427 : term477 = term283.
Proof. exact (@lem1982721 term283). Qed.
Lemma lem5416428 (_69910 : int) (_69911 : int) : (term511 _69910 _69911) = term283.
Proof. exact (TRANS (@lem5416426 _69910 _69911) (@lem5416427)). Qed.
Lemma lem5416429 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5416430 (_69910 : int) (_69911 : int) : (term515 _69910 _69911) = term479.
Proof. exact (MK_COMB (@lem5416429) (@lem5416428 _69910 _69911)). Qed.
Lemma lem5416431 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5416432 (_69910 : int) (_69911 : int) : (term510 _69910 _69911) = term480.
Proof. exact (MK_COMB (@lem5416430 _69910 _69911) (@lem5416431)). Qed.
Lemma lem5416433 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : term480.
Proof. exact (EQ_MP (@lem5416432 _69910 _69911) (@lem5416201 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416435 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5416436 : term480 = term481.
Proof. exact (@lem5416435 term153 term283). Qed.
Lemma lem5416438 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5416439 : term283 = term286.
Proof. exact (@lem5416438 term257). Qed.
Lemma lem5416441 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416442 : term153 = term211.
Proof. exact (@lem5416441 (NUMERAL 0)). Qed.
Lemma lem5416443 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5416444 : term155 = term482.
Proof. exact (MK_COMB (@lem5416443) (@lem5416442)). Qed.
Lemma lem5416445 : term481 = term483.
Proof. exact (MK_COMB (@lem5416444) (@lem5416439)). Qed.
Lemma lem5416446 : term484.
Proof. exact (@lem1980026 term153 term170 term283 term170). Qed.
Lemma lem5416448 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416449 : term245 = term246.
Proof. exact (@lem5416448 (NUMERAL 0) term69). Qed.
Lemma lem5416450 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416451 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416452 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416451 h1) (fun h1 : term246 = True => @lem5416450)). Qed.
Lemma lem5416453 : term246 = True.
Proof. exact (EQ_MP (@lem5416452) (@lem5416450)). Qed.
Lemma lem5416454 : term245 = True.
Proof. exact (TRANS (@lem5416449) (@lem5416453)). Qed.
Lemma lem5416455 : True = term245.
Proof. exact (SYM (@lem5416454)). Qed.
Lemma lem5416456 : term245.
Proof. exact (EQ_MP (@lem5416455) (@lem0)). Qed.
Lemma lem5416457 : term485.
Proof. exact (@lem5416446 (@lem5416456)). Qed.
Lemma lem5416459 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416460 : term245 = term246.
Proof. exact (@lem5416459 (NUMERAL 0) term69). Qed.
Lemma lem5416461 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416462 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416463 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416462 h1) (fun h1 : term246 = True => @lem5416461)). Qed.
Lemma lem5416464 : term246 = True.
Proof. exact (EQ_MP (@lem5416463) (@lem5416461)). Qed.
Lemma lem5416465 : term245 = True.
Proof. exact (TRANS (@lem5416460) (@lem5416464)). Qed.
Lemma lem5416466 : True = term245.
Proof. exact (SYM (@lem5416465)). Qed.
Lemma lem5416467 : term245.
Proof. exact (EQ_MP (@lem5416466) (@lem0)). Qed.
Lemma lem5416468 : term483 = term486.
Proof. exact (@lem5416457 (@lem5416467)). Qed.
Lemma lem5416470 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5416471 : term487 = term488.
Proof. exact (@lem5416470 term257 term69). Qed.
Lemma lem5416472 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5416473 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5416474 : term264 = term257.
Proof. exact (EQ_MP (@lem5416473) (@lem5416472)). Qed.
Lemma lem5416475 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416476 : term262 = term243.
Proof. exact (MK_COMB (@lem5416475) (@lem5416474)). Qed.
Lemma lem5416477 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416478 : term488 = term283.
Proof. exact (MK_COMB (@lem5416477) (@lem5416476)). Qed.
Lemma lem5416479 : term487 = term283.
Proof. exact (TRANS (@lem5416471) (@lem5416478)). Qed.
Lemma lem5416481 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416482 : term418 = term153.
Proof. exact (@lem5416481 term69). Qed.
Lemma lem5416483 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5416484 : term489 = term155.
Proof. exact (MK_COMB (@lem5416483) (@lem5416482)). Qed.
Lemma lem5416485 : term486 = term481.
Proof. exact (MK_COMB (@lem5416484) (@lem5416479)). Qed.
Lemma lem5416487 (m : nat) (n : nat) : (term490 m n) = (term491 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5416488 : term481 = term492.
Proof. exact (@lem5416487 (NUMERAL 0) term257). Qed.
Lemma lem5416489 : term493 = term255.
Proof. exact (@lem912803). Qed.
Lemma lem5416490 (h1 : term493 = term255) : (term257 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term255 h1). Qed.
Lemma lem5416491 : (term493 = term255) = ((term257 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term493 = term255 => @lem5416490 h1) (fun h1 : (term257 = (NUMERAL 0)) = False => @lem5416489)). Qed.
Lemma lem5416492 : (term257 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5416491) (@lem5416489)). Qed.
Lemma lem5416493 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5416494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5416495 : term494 = (and True).
Proof. exact (MK_COMB (@lem5416494) (@lem5416493)). Qed.
Lemma lem5416496 : term492 = (True /\ False).
Proof. exact (MK_COMB (@lem5416495) (@lem5416492)). Qed.
Lemma lem5416498 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5416499 : term492 = False.
Proof. exact (TRANS (@lem5416496) (@lem5416498)). Qed.
Lemma lem5416500 : term481 = False.
Proof. exact (TRANS (@lem5416488) (@lem5416499)). Qed.
Lemma lem5416501 : term486 = False.
Proof. exact (TRANS (@lem5416485) (@lem5416500)). Qed.
Lemma lem5416502 : term483 = False.
Proof. exact (TRANS (@lem5416468) (@lem5416501)). Qed.
Lemma lem5416503 : term481 = False.
Proof. exact (TRANS (@lem5416445) (@lem5416502)). Qed.
Lemma lem5416504 : term480 = False.
Proof. exact (TRANS (@lem5416436) (@lem5416503)). Qed.
Lemma lem5416505 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term495 _69909 _69910 _69911) : False.
Proof. exact (EQ_MP (@lem5416504) (@lem5416433 _69909 _69910 _69911 h1)). Qed.
Lemma lem5416506 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term403 _69909 _69910 _69911) : False.
Proof. exact (or_elim (@lem5415013 _69909 _69910 _69911 h1) (fun h0 : term409 _69909 _69910 _69911 => @lem5415759 _69909 _69910 _69911 h0) (fun h0 : term495 _69909 _69910 _69911 => @lem5416505 _69909 _69910 _69911 h0)). Qed.
Lemma lem5416507 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term399 _69909 _69910 _69911) : term399 _69909 _69910 _69911.
Proof. exact (h1). Qed.
Lemma lem5416508 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term516 _69910 _69909 _69911.
Proof. exact (h1). Qed.
Lemma lem5416509 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term400 _69910 _69909 _69911.
Proof. exact (proj2 (@lem5416508 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416511 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term387 _69910 _69909 _69911.
Proof. exact (proj2 (@lem5416509 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416513 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term374 _69910 _69909 _69911.
Proof. exact (proj2 (@lem5416511 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416515 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term361 _69910 _69909 _69911.
Proof. exact (proj2 (@lem5416513 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416516 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term292 _69909 _69910.
Proof. exact (proj1 (@lem5416513 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416518 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term338 _69909 _69910 _69911.
Proof. exact (proj1 (@lem5416515 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416519 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term337 _69910 _69911.
Proof. exact (proj2 (@lem5416518 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416520 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term321 _69909 _69911.
Proof. exact (proj1 (@lem5416518 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416522 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5416523 : term410 = term245.
Proof. exact (@lem5416522 term153 term170). Qed.
Lemma lem5416525 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416526 : term170 = term237.
Proof. exact (@lem5416525 term69). Qed.
Lemma lem5416528 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416529 : term153 = term211.
Proof. exact (@lem5416528 (NUMERAL 0)). Qed.
Lemma lem5416530 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5416531 : term411 = term412.
Proof. exact (MK_COMB (@lem5416530) (@lem5416529)). Qed.
Lemma lem5416532 : term245 = term413.
Proof. exact (MK_COMB (@lem5416531) (@lem5416526)). Qed.
Lemma lem5416533 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5416535 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416536 : term245 = term246.
Proof. exact (@lem5416535 (NUMERAL 0) term69). Qed.
Lemma lem5416537 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416538 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416539 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416538 h1) (fun h1 : term246 = True => @lem5416537)). Qed.
Lemma lem5416540 : term246 = True.
Proof. exact (EQ_MP (@lem5416539) (@lem5416537)). Qed.
Lemma lem5416541 : term245 = True.
Proof. exact (TRANS (@lem5416536) (@lem5416540)). Qed.
Lemma lem5416542 : True = term245.
Proof. exact (SYM (@lem5416541)). Qed.
Lemma lem5416543 : term245.
Proof. exact (EQ_MP (@lem5416542) (@lem0)). Qed.
Lemma lem5416544 : term415.
Proof. exact (@lem5416533 (@lem5416543)). Qed.
Lemma lem5416546 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416547 : term245 = term246.
Proof. exact (@lem5416546 (NUMERAL 0) term69). Qed.
Lemma lem5416548 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416549 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416550 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416549 h1) (fun h1 : term246 = True => @lem5416548)). Qed.
Lemma lem5416551 : term246 = True.
Proof. exact (EQ_MP (@lem5416550) (@lem5416548)). Qed.
Lemma lem5416552 : term245 = True.
Proof. exact (TRANS (@lem5416547) (@lem5416551)). Qed.
Lemma lem5416553 : True = term245.
Proof. exact (SYM (@lem5416552)). Qed.
Lemma lem5416554 : term245.
Proof. exact (EQ_MP (@lem5416553) (@lem0)). Qed.
Lemma lem5416555 : term413 = term416.
Proof. exact (@lem5416544 (@lem5416554)). Qed.
Lemma lem5416557 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416558 : term223 = term224.
Proof. exact (@lem5416557 term69 term69). Qed.
Lemma lem5416559 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416560 : term226 = term69.
Proof. exact (EQ_MP (@lem5416559) (@lem940073)). Qed.
Lemma lem5416561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416562 : term224 = term170.
Proof. exact (MK_COMB (@lem5416561) (@lem5416560)). Qed.
Lemma lem5416563 : term223 = term170.
Proof. exact (TRANS (@lem5416558) (@lem5416562)). Qed.
Lemma lem5416565 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416566 : term418 = term153.
Proof. exact (@lem5416565 term69). Qed.
Lemma lem5416567 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5416568 : term419 = term411.
Proof. exact (MK_COMB (@lem5416567) (@lem5416566)). Qed.
Lemma lem5416569 : term416 = term245.
Proof. exact (MK_COMB (@lem5416568) (@lem5416563)). Qed.
Lemma lem5416571 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416572 : term245 = term246.
Proof. exact (@lem5416571 (NUMERAL 0) term69). Qed.
Lemma lem5416573 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416574 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416575 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416574 h1) (fun h1 : term246 = True => @lem5416573)). Qed.
Lemma lem5416576 : term246 = True.
Proof. exact (EQ_MP (@lem5416575) (@lem5416573)). Qed.
Lemma lem5416577 : term245 = True.
Proof. exact (TRANS (@lem5416572) (@lem5416576)). Qed.
Lemma lem5416578 : term416 = True.
Proof. exact (TRANS (@lem5416569) (@lem5416577)). Qed.
Lemma lem5416579 : term413 = True.
Proof. exact (TRANS (@lem5416555) (@lem5416578)). Qed.
Lemma lem5416580 : term245 = True.
Proof. exact (TRANS (@lem5416532) (@lem5416579)). Qed.
Lemma lem5416581 : term410 = True.
Proof. exact (TRANS (@lem5416523) (@lem5416580)). Qed.
Lemma lem5416582 : True = term410.
Proof. exact (SYM (@lem5416581)). Qed.
Lemma lem5416583 : term410.
Proof. exact (EQ_MP (@lem5416582) (@lem0)). Qed.
Lemma lem5416584 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term517 _69910 _69911.
Proof. exact (conj (@lem5416583) (@lem5416519 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416586 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5416587 (_69910 : int) (_69911 : int) : term518 _69910 _69911.
Proof. exact (@lem5416586 term170 (term334 _69910 _69911)). Qed.
Lemma lem5416588 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term519 _69910 _69911.
Proof. exact (@lem5416587 _69910 _69911 (@lem5416584 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416589 (_69910 : int) (_69911 : int) : (term520 _69910 _69911) = (term334 _69910 _69911).
Proof. exact (@lem1982733 (term334 _69910 _69911)). Qed.
Lemma lem5416590 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5416591 (_69910 : int) (_69911 : int) : (term521 _69910 _69911) = (term336 _69910 _69911).
Proof. exact (MK_COMB (@lem5416590) (@lem5416589 _69910 _69911)). Qed.
Lemma lem5416592 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5416593 (_69910 : int) (_69911 : int) : (term519 _69910 _69911) = (term337 _69910 _69911).
Proof. exact (MK_COMB (@lem5416591 _69910 _69911) (@lem5416592)). Qed.
Lemma lem5416594 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term337 _69910 _69911.
Proof. exact (EQ_MP (@lem5416593 _69910 _69911) (@lem5416588 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416596 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5416597 : term410 = term245.
Proof. exact (@lem5416596 term153 term170). Qed.
Lemma lem5416599 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416600 : term170 = term237.
Proof. exact (@lem5416599 term69). Qed.
Lemma lem5416602 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416603 : term153 = term211.
Proof. exact (@lem5416602 (NUMERAL 0)). Qed.
Lemma lem5416604 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5416605 : term411 = term412.
Proof. exact (MK_COMB (@lem5416604) (@lem5416603)). Qed.
Lemma lem5416606 : term245 = term413.
Proof. exact (MK_COMB (@lem5416605) (@lem5416600)). Qed.
Lemma lem5416607 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5416609 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416610 : term245 = term246.
Proof. exact (@lem5416609 (NUMERAL 0) term69). Qed.
Lemma lem5416611 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416612 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416613 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416612 h1) (fun h1 : term246 = True => @lem5416611)). Qed.
Lemma lem5416614 : term246 = True.
Proof. exact (EQ_MP (@lem5416613) (@lem5416611)). Qed.
Lemma lem5416615 : term245 = True.
Proof. exact (TRANS (@lem5416610) (@lem5416614)). Qed.
Lemma lem5416616 : True = term245.
Proof. exact (SYM (@lem5416615)). Qed.
Lemma lem5416617 : term245.
Proof. exact (EQ_MP (@lem5416616) (@lem0)). Qed.
Lemma lem5416618 : term415.
Proof. exact (@lem5416607 (@lem5416617)). Qed.
Lemma lem5416620 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416621 : term245 = term246.
Proof. exact (@lem5416620 (NUMERAL 0) term69). Qed.
Lemma lem5416622 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416623 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416624 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416623 h1) (fun h1 : term246 = True => @lem5416622)). Qed.
Lemma lem5416625 : term246 = True.
Proof. exact (EQ_MP (@lem5416624) (@lem5416622)). Qed.
Lemma lem5416626 : term245 = True.
Proof. exact (TRANS (@lem5416621) (@lem5416625)). Qed.
Lemma lem5416627 : True = term245.
Proof. exact (SYM (@lem5416626)). Qed.
Lemma lem5416628 : term245.
Proof. exact (EQ_MP (@lem5416627) (@lem0)). Qed.
Lemma lem5416629 : term413 = term416.
Proof. exact (@lem5416618 (@lem5416628)). Qed.
Lemma lem5416631 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416632 : term223 = term224.
Proof. exact (@lem5416631 term69 term69). Qed.
Lemma lem5416633 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416634 : term226 = term69.
Proof. exact (EQ_MP (@lem5416633) (@lem940073)). Qed.
Lemma lem5416635 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416636 : term224 = term170.
Proof. exact (MK_COMB (@lem5416635) (@lem5416634)). Qed.
Lemma lem5416637 : term223 = term170.
Proof. exact (TRANS (@lem5416632) (@lem5416636)). Qed.
Lemma lem5416639 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416640 : term418 = term153.
Proof. exact (@lem5416639 term69). Qed.
Lemma lem5416641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5416642 : term419 = term411.
Proof. exact (MK_COMB (@lem5416641) (@lem5416640)). Qed.
Lemma lem5416643 : term416 = term245.
Proof. exact (MK_COMB (@lem5416642) (@lem5416637)). Qed.
Lemma lem5416645 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416646 : term245 = term246.
Proof. exact (@lem5416645 (NUMERAL 0) term69). Qed.
Lemma lem5416647 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416648 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416649 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416648 h1) (fun h1 : term246 = True => @lem5416647)). Qed.
Lemma lem5416650 : term246 = True.
Proof. exact (EQ_MP (@lem5416649) (@lem5416647)). Qed.
Lemma lem5416651 : term245 = True.
Proof. exact (TRANS (@lem5416646) (@lem5416650)). Qed.
Lemma lem5416652 : term416 = True.
Proof. exact (TRANS (@lem5416643) (@lem5416651)). Qed.
Lemma lem5416653 : term413 = True.
Proof. exact (TRANS (@lem5416629) (@lem5416652)). Qed.
Lemma lem5416654 : term245 = True.
Proof. exact (TRANS (@lem5416606) (@lem5416653)). Qed.
Lemma lem5416655 : term410 = True.
Proof. exact (TRANS (@lem5416597) (@lem5416654)). Qed.
Lemma lem5416656 : True = term410.
Proof. exact (SYM (@lem5416655)). Qed.
Lemma lem5416657 : term410.
Proof. exact (EQ_MP (@lem5416656) (@lem0)). Qed.
Lemma lem5416658 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term426 _69909 _69910.
Proof. exact (conj (@lem5416657) (@lem5416516 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416660 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5416661 (_69909 : int) (_69910 : int) : term427 _69909 _69910.
Proof. exact (@lem5416660 term170 (term289 _69909 _69910)). Qed.
Lemma lem5416662 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term428 _69909 _69910.
Proof. exact (@lem5416661 _69909 _69910 (@lem5416658 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416663 (_69909 : int) (_69910 : int) : (term429 _69909 _69910) = (term289 _69909 _69910).
Proof. exact (@lem1982733 (term289 _69909 _69910)). Qed.
Lemma lem5416664 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5416665 (_69909 : int) (_69910 : int) : (term430 _69909 _69910) = (term291 _69909 _69910).
Proof. exact (MK_COMB (@lem5416664) (@lem5416663 _69909 _69910)). Qed.
Lemma lem5416666 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5416667 (_69909 : int) (_69910 : int) : (term428 _69909 _69910) = (term292 _69909 _69910).
Proof. exact (MK_COMB (@lem5416665 _69909 _69910) (@lem5416666)). Qed.
Lemma lem5416668 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term292 _69909 _69910.
Proof. exact (EQ_MP (@lem5416667 _69909 _69910) (@lem5416662 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416669 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term522 _69909 _69910 _69911.
Proof. exact (conj (@lem5416668 _69910 _69909 _69911 h1) (@lem5416594 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416671 (x : real) (y : real) : term432 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5416672 (_69909 : int) (_69910 : int) (_69911 : int) : term523 _69909 _69910 _69911.
Proof. exact (@lem5416671 (term289 _69909 _69910) (term334 _69910 _69911)). Qed.
Lemma lem5416673 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term524 _69909 _69910 _69911.
Proof. exact (@lem5416672 _69909 _69910 _69911 (@lem5416669 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416674 (_69909 : int) (_69910 : int) (_69911 : int) : (term525 _69909 _69910 _69911) = (term526 _69909 _69910 _69911).
Proof. exact (@lem1982755 (real_of_int _69909) (term288 _69910) (term334 _69910 _69911)). Qed.
Lemma lem5416675 (_69910 : int) (_69911 : int) : (term527 _69910 _69911) = (term528 _69910 _69911).
Proof. exact (@lem1982753 (term310 _69910) (real_of_int _69910) term283 (term333 _69911)). Qed.
Lemma lem5416676 (_69910 : int) : (term439 _69910) = (term440 _69910).
Proof. exact (@lem1982713 term214 (real_of_int _69910)). Qed.
Lemma lem5416678 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416679 : term170 = term237.
Proof. exact (@lem5416678 term69). Qed.
Lemma lem5416681 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5416682 : term214 = term215.
Proof. exact (@lem5416681 term69). Qed.
Lemma lem5416683 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416684 : term441 = term442.
Proof. exact (MK_COMB (@lem5416683) (@lem5416682)). Qed.
Lemma lem5416685 : term443 = term444.
Proof. exact (MK_COMB (@lem5416684) (@lem5416679)). Qed.
Lemma lem5416686 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5416688 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416689 : term245 = term246.
Proof. exact (@lem5416688 (NUMERAL 0) term69). Qed.
Lemma lem5416690 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416691 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416692 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416691 h1) (fun h1 : term246 = True => @lem5416690)). Qed.
Lemma lem5416693 : term246 = True.
Proof. exact (EQ_MP (@lem5416692) (@lem5416690)). Qed.
Lemma lem5416694 : term245 = True.
Proof. exact (TRANS (@lem5416689) (@lem5416693)). Qed.
Lemma lem5416695 : True = term245.
Proof. exact (SYM (@lem5416694)). Qed.
Lemma lem5416696 : term245.
Proof. exact (EQ_MP (@lem5416695) (@lem0)). Qed.
Lemma lem5416697 : term446.
Proof. exact (@lem5416686 (@lem5416696)). Qed.
Lemma lem5416699 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416700 : term245 = term246.
Proof. exact (@lem5416699 (NUMERAL 0) term69). Qed.
Lemma lem5416701 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416702 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416703 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416702 h1) (fun h1 : term246 = True => @lem5416701)). Qed.
Lemma lem5416704 : term246 = True.
Proof. exact (EQ_MP (@lem5416703) (@lem5416701)). Qed.
Lemma lem5416705 : term245 = True.
Proof. exact (TRANS (@lem5416700) (@lem5416704)). Qed.
Lemma lem5416706 : True = term245.
Proof. exact (SYM (@lem5416705)). Qed.
Lemma lem5416707 : term245.
Proof. exact (EQ_MP (@lem5416706) (@lem0)). Qed.
Lemma lem5416708 : term447.
Proof. exact (@lem5416697 (@lem5416707)). Qed.
Lemma lem5416710 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416711 : term245 = term246.
Proof. exact (@lem5416710 (NUMERAL 0) term69). Qed.
Lemma lem5416712 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416713 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416714 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416713 h1) (fun h1 : term246 = True => @lem5416712)). Qed.
Lemma lem5416715 : term246 = True.
Proof. exact (EQ_MP (@lem5416714) (@lem5416712)). Qed.
Lemma lem5416716 : term245 = True.
Proof. exact (TRANS (@lem5416711) (@lem5416715)). Qed.
Lemma lem5416717 : True = term245.
Proof. exact (SYM (@lem5416716)). Qed.
Lemma lem5416718 : term245.
Proof. exact (EQ_MP (@lem5416717) (@lem0)). Qed.
Lemma lem5416719 : term448.
Proof. exact (@lem5416708 (@lem5416718)). Qed.
Lemma lem5416721 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416722 : term223 = term224.
Proof. exact (@lem5416721 term69 term69). Qed.
Lemma lem5416723 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416724 : term226 = term69.
Proof. exact (EQ_MP (@lem5416723) (@lem940073)). Qed.
Lemma lem5416725 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416726 : term224 = term170.
Proof. exact (MK_COMB (@lem5416725) (@lem5416724)). Qed.
Lemma lem5416727 : term223 = term170.
Proof. exact (TRANS (@lem5416722) (@lem5416726)). Qed.
Lemma lem5416729 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5416730 : term298 = term301.
Proof. exact (@lem5416729 term69 term69). Qed.
Lemma lem5416731 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416732 : term226 = term69.
Proof. exact (EQ_MP (@lem5416731) (@lem940073)). Qed.
Lemma lem5416733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416734 : term224 = term170.
Proof. exact (MK_COMB (@lem5416733) (@lem5416732)). Qed.
Lemma lem5416735 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416736 : term301 = term214.
Proof. exact (MK_COMB (@lem5416735) (@lem5416734)). Qed.
Lemma lem5416737 : term298 = term214.
Proof. exact (TRANS (@lem5416730) (@lem5416736)). Qed.
Lemma lem5416738 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416739 : term449 = term441.
Proof. exact (MK_COMB (@lem5416738) (@lem5416737)). Qed.
Lemma lem5416740 : term450 = term443.
Proof. exact (MK_COMB (@lem5416739) (@lem5416727)). Qed.
Lemma lem5416742 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5416743 : term443 = term153.
Proof. exact (@lem5416742 term69). Qed.
Lemma lem5416744 : term450 = term153.
Proof. exact (TRANS (@lem5416740) (@lem5416743)). Qed.
Lemma lem5416745 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416746 : term452 = term453.
Proof. exact (MK_COMB (@lem5416745) (@lem5416744)). Qed.
Lemma lem5416747 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5416748 : term454 = term418.
Proof. exact (MK_COMB (@lem5416746) (@lem5416747)). Qed.
Lemma lem5416750 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416751 : term418 = term153.
Proof. exact (@lem5416750 term69). Qed.
Lemma lem5416752 : term454 = term153.
Proof. exact (TRANS (@lem5416748) (@lem5416751)). Qed.
Lemma lem5416754 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416755 : term223 = term224.
Proof. exact (@lem5416754 term69 term69). Qed.
Lemma lem5416756 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416757 : term226 = term69.
Proof. exact (EQ_MP (@lem5416756) (@lem940073)). Qed.
Lemma lem5416758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416759 : term224 = term170.
Proof. exact (MK_COMB (@lem5416758) (@lem5416757)). Qed.
Lemma lem5416760 : term223 = term170.
Proof. exact (TRANS (@lem5416755) (@lem5416759)). Qed.
Lemma lem5416761 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5416762 : term455 = term418.
Proof. exact (MK_COMB (@lem5416761) (@lem5416760)). Qed.
Lemma lem5416764 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416765 : term418 = term153.
Proof. exact (@lem5416764 term69). Qed.
Lemma lem5416766 : term455 = term153.
Proof. exact (TRANS (@lem5416762) (@lem5416765)). Qed.
Lemma lem5416767 : term153 = term455.
Proof. exact (SYM (@lem5416766)). Qed.
Lemma lem5416768 : term454 = term455.
Proof. exact (TRANS (@lem5416752) (@lem5416767)). Qed.
Lemma lem5416769 : term444 = term211.
Proof. exact (@lem5416719 (@lem5416768)). Qed.
Lemma lem5416770 : term443 = term211.
Proof. exact (TRANS (@lem5416685) (@lem5416769)). Qed.
Lemma lem5416772 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5416773 : term211 = term153.
Proof. exact (@lem5416772 term153). Qed.
Lemma lem5416774 : term443 = term153.
Proof. exact (TRANS (@lem5416770) (@lem5416773)). Qed.
Lemma lem5416775 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416776 : term456 = term453.
Proof. exact (MK_COMB (@lem5416775) (@lem5416774)). Qed.
Lemma lem5416777 (_69910 : int) : (real_of_int _69910) = (real_of_int _69910).
Proof. exact (eq_refl (real_of_int _69910)). Qed.
Lemma lem5416778 (_69910 : int) : (term440 _69910) = (term457 _69910).
Proof. exact (MK_COMB (@lem5416776) (@lem5416777 _69910)). Qed.
Lemma lem5416779 (_69910 : int) : (term439 _69910) = (term457 _69910).
Proof. exact (TRANS (@lem5416676 _69910) (@lem5416778 _69910)). Qed.
Lemma lem5416780 (_69910 : int) : (term457 _69910) = term153.
Proof. exact (@lem1982719 (real_of_int _69910)). Qed.
Lemma lem5416781 (_69910 : int) : (term439 _69910) = term153.
Proof. exact (TRANS (@lem5416779 _69910) (@lem5416780 _69910)). Qed.
Lemma lem5416782 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416783 (_69910 : int) : (term458 _69910) = term459.
Proof. exact (MK_COMB (@lem5416782) (@lem5416781 _69910)). Qed.
Lemma lem5416784 (_69911 : int) : (term529 _69911) = (term530 _69911).
Proof. exact (@lem1982757 (term310 _69911) term283 term170). Qed.
Lemma lem5416786 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416787 : term170 = term237.
Proof. exact (@lem5416786 term69). Qed.
Lemma lem5416789 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5416790 : term283 = term286.
Proof. exact (@lem5416789 term257). Qed.
Lemma lem5416791 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416792 : term531 = term532.
Proof. exact (MK_COMB (@lem5416791) (@lem5416790)). Qed.
Lemma lem5416793 : term533 = term534.
Proof. exact (MK_COMB (@lem5416792) (@lem5416787)). Qed.
Lemma lem5416794 : term535.
Proof. exact (@lem1981473 term283 term170 term170 term170 term214 term170). Qed.
Lemma lem5416796 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416797 : term245 = term246.
Proof. exact (@lem5416796 (NUMERAL 0) term69). Qed.
Lemma lem5416798 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416799 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416800 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416799 h1) (fun h1 : term246 = True => @lem5416798)). Qed.
Lemma lem5416801 : term246 = True.
Proof. exact (EQ_MP (@lem5416800) (@lem5416798)). Qed.
Lemma lem5416802 : term245 = True.
Proof. exact (TRANS (@lem5416797) (@lem5416801)). Qed.
Lemma lem5416803 : True = term245.
Proof. exact (SYM (@lem5416802)). Qed.
Lemma lem5416804 : term245.
Proof. exact (EQ_MP (@lem5416803) (@lem0)). Qed.
Lemma lem5416805 : term536.
Proof. exact (@lem5416794 (@lem5416804)). Qed.
Lemma lem5416807 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416808 : term245 = term246.
Proof. exact (@lem5416807 (NUMERAL 0) term69). Qed.
Lemma lem5416809 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416810 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416811 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416810 h1) (fun h1 : term246 = True => @lem5416809)). Qed.
Lemma lem5416812 : term246 = True.
Proof. exact (EQ_MP (@lem5416811) (@lem5416809)). Qed.
Lemma lem5416813 : term245 = True.
Proof. exact (TRANS (@lem5416808) (@lem5416812)). Qed.
Lemma lem5416814 : True = term245.
Proof. exact (SYM (@lem5416813)). Qed.
Lemma lem5416815 : term245.
Proof. exact (EQ_MP (@lem5416814) (@lem0)). Qed.
Lemma lem5416816 : term537.
Proof. exact (@lem5416805 (@lem5416815)). Qed.
Lemma lem5416818 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416819 : term245 = term246.
Proof. exact (@lem5416818 (NUMERAL 0) term69). Qed.
Lemma lem5416820 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416821 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416822 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416821 h1) (fun h1 : term246 = True => @lem5416820)). Qed.
Lemma lem5416823 : term246 = True.
Proof. exact (EQ_MP (@lem5416822) (@lem5416820)). Qed.
Lemma lem5416824 : term245 = True.
Proof. exact (TRANS (@lem5416819) (@lem5416823)). Qed.
Lemma lem5416825 : True = term245.
Proof. exact (SYM (@lem5416824)). Qed.
Lemma lem5416826 : term245.
Proof. exact (EQ_MP (@lem5416825) (@lem0)). Qed.
Lemma lem5416827 : term538.
Proof. exact (@lem5416816 (@lem5416826)). Qed.
Lemma lem5416829 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416830 : term223 = term224.
Proof. exact (@lem5416829 term69 term69). Qed.
Lemma lem5416831 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416832 : term226 = term69.
Proof. exact (EQ_MP (@lem5416831) (@lem940073)). Qed.
Lemma lem5416833 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416834 : term224 = term170.
Proof. exact (MK_COMB (@lem5416833) (@lem5416832)). Qed.
Lemma lem5416835 : term223 = term170.
Proof. exact (TRANS (@lem5416830) (@lem5416834)). Qed.
Lemma lem5416837 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5416838 : term487 = term488.
Proof. exact (@lem5416837 term257 term69). Qed.
Lemma lem5416839 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5416840 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5416841 : term264 = term257.
Proof. exact (EQ_MP (@lem5416840) (@lem5416839)). Qed.
Lemma lem5416842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416843 : term262 = term243.
Proof. exact (MK_COMB (@lem5416842) (@lem5416841)). Qed.
Lemma lem5416844 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416845 : term488 = term283.
Proof. exact (MK_COMB (@lem5416844) (@lem5416843)). Qed.
Lemma lem5416846 : term487 = term283.
Proof. exact (TRANS (@lem5416838) (@lem5416845)). Qed.
Lemma lem5416847 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416848 : term539 = term531.
Proof. exact (MK_COMB (@lem5416847) (@lem5416846)). Qed.
Lemma lem5416849 : term540 = term533.
Proof. exact (MK_COMB (@lem5416848) (@lem5416835)). Qed.
Lemma lem5416852 : term541 = term214.
Proof. exact (@lem1367767 term69 term69). Qed.
Lemma lem5416853 : term254 = term255.
Proof. exact (@lem706885). Qed.
Lemma lem5416854 : (term254 = term255) = (term256 = term257).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term255). Qed.
Lemma lem5416855 : term256 = term257.
Proof. exact (EQ_MP (@lem5416854) (@lem5416853)). Qed.
Lemma lem5416856 : term257 = term256.
Proof. exact (SYM (@lem5416855)). Qed.
Lemma lem5416857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416858 : term243 = term253.
Proof. exact (MK_COMB (@lem5416857) (@lem5416856)). Qed.
Lemma lem5416859 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416860 : term283 = term542.
Proof. exact (MK_COMB (@lem5416859) (@lem5416858)). Qed.
Lemma lem5416861 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5416862 : term531 = term543.
Proof. exact (MK_COMB (@lem5416861) (@lem5416860)). Qed.
Lemma lem5416863 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5416864 : term533 = term541.
Proof. exact (MK_COMB (@lem5416862) (@lem5416863)). Qed.
Lemma lem5416865 : term533 = term214.
Proof. exact (TRANS (@lem5416864) (@lem5416852)). Qed.
Lemma lem5416866 : term540 = term214.
Proof. exact (TRANS (@lem5416849) (@lem5416865)). Qed.
Lemma lem5416867 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5416868 : term544 = term216.
Proof. exact (MK_COMB (@lem5416867) (@lem5416866)). Qed.
Lemma lem5416869 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5416870 : term545 = term298.
Proof. exact (MK_COMB (@lem5416868) (@lem5416869)). Qed.
Lemma lem5416872 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5416873 : term298 = term301.
Proof. exact (@lem5416872 term69 term69). Qed.
Lemma lem5416874 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416875 : term226 = term69.
Proof. exact (EQ_MP (@lem5416874) (@lem940073)). Qed.
Lemma lem5416876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416877 : term224 = term170.
Proof. exact (MK_COMB (@lem5416876) (@lem5416875)). Qed.
Lemma lem5416878 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416879 : term301 = term214.
Proof. exact (MK_COMB (@lem5416878) (@lem5416877)). Qed.
Lemma lem5416880 : term298 = term214.
Proof. exact (TRANS (@lem5416873) (@lem5416879)). Qed.
Lemma lem5416881 : term545 = term214.
Proof. exact (TRANS (@lem5416870) (@lem5416880)). Qed.
Lemma lem5416883 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416884 : term223 = term224.
Proof. exact (@lem5416883 term69 term69). Qed.
Lemma lem5416885 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416886 : term226 = term69.
Proof. exact (EQ_MP (@lem5416885) (@lem940073)). Qed.
Lemma lem5416887 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416888 : term224 = term170.
Proof. exact (MK_COMB (@lem5416887) (@lem5416886)). Qed.
Lemma lem5416889 : term223 = term170.
Proof. exact (TRANS (@lem5416884) (@lem5416888)). Qed.
Lemma lem5416890 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem5416891 : term546 = term298.
Proof. exact (MK_COMB (@lem5416890) (@lem5416889)). Qed.
Lemma lem5416893 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5416894 : term298 = term301.
Proof. exact (@lem5416893 term69 term69). Qed.
Lemma lem5416895 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416896 : term226 = term69.
Proof. exact (EQ_MP (@lem5416895) (@lem940073)). Qed.
Lemma lem5416897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416898 : term224 = term170.
Proof. exact (MK_COMB (@lem5416897) (@lem5416896)). Qed.
Lemma lem5416899 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5416900 : term301 = term214.
Proof. exact (MK_COMB (@lem5416899) (@lem5416898)). Qed.
Lemma lem5416901 : term298 = term214.
Proof. exact (TRANS (@lem5416894) (@lem5416900)). Qed.
Lemma lem5416902 : term546 = term214.
Proof. exact (TRANS (@lem5416891) (@lem5416901)). Qed.
Lemma lem5416903 : term214 = term546.
Proof. exact (SYM (@lem5416902)). Qed.
Lemma lem5416904 : term545 = term546.
Proof. exact (TRANS (@lem5416881) (@lem5416903)). Qed.
Lemma lem5416905 : term534 = term215.
Proof. exact (@lem5416827 (@lem5416904)). Qed.
Lemma lem5416906 : term533 = term215.
Proof. exact (TRANS (@lem5416793) (@lem5416905)). Qed.
Lemma lem5416908 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5416909 : term215 = term214.
Proof. exact (@lem5416908 term214). Qed.
Lemma lem5416910 : term533 = term214.
Proof. exact (TRANS (@lem5416906) (@lem5416909)). Qed.
Lemma lem5416911 (_69911 : int) : (term287 _69911) = (term287 _69911).
Proof. exact (eq_refl (term287 _69911)). Qed.
Lemma lem5416912 (_69911 : int) : (term530 _69911) = (term304 _69911).
Proof. exact (MK_COMB (@lem5416911 _69911) (@lem5416910)). Qed.
Lemma lem5416913 (_69911 : int) : (term529 _69911) = (term304 _69911).
Proof. exact (TRANS (@lem5416784 _69911) (@lem5416912 _69911)). Qed.
Lemma lem5416914 (_69910 : int) (_69911 : int) : (term528 _69910 _69911) = (term547 _69911).
Proof. exact (MK_COMB (@lem5416783 _69910) (@lem5416913 _69911)). Qed.
Lemma lem5416915 (_69910 : int) (_69911 : int) : (term527 _69910 _69911) = (term547 _69911).
Proof. exact (TRANS (@lem5416675 _69910 _69911) (@lem5416914 _69910 _69911)). Qed.
Lemma lem5416916 (_69911 : int) : (term547 _69911) = (term304 _69911).
Proof. exact (@lem1982721 (term304 _69911)). Qed.
Lemma lem5416917 (_69910 : int) (_69911 : int) : (term527 _69910 _69911) = (term304 _69911).
Proof. exact (TRANS (@lem5416915 _69910 _69911) (@lem5416916 _69911)). Qed.
Lemma lem5416918 (_69909 : int) : (term171 _69909) = (term171 _69909).
Proof. exact (eq_refl (term171 _69909)). Qed.
Lemma lem5416919 (_69910 : int) (_69909 : int) (_69911 : int) : (term526 _69909 _69910 _69911) = (term305 _69909 _69911).
Proof. exact (MK_COMB (@lem5416918 _69909) (@lem5416917 _69910 _69911)). Qed.
Lemma lem5416920 (_69910 : int) (_69909 : int) (_69911 : int) : (term525 _69909 _69910 _69911) = (term305 _69909 _69911).
Proof. exact (TRANS (@lem5416674 _69909 _69910 _69911) (@lem5416919 _69910 _69909 _69911)). Qed.
Lemma lem5416921 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5416922 (_69910 : int) (_69909 : int) (_69911 : int) : (term548 _69909 _69910 _69911) = (term307 _69909 _69911).
Proof. exact (MK_COMB (@lem5416921) (@lem5416920 _69910 _69909 _69911)). Qed.
Lemma lem5416923 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5416924 (_69910 : int) (_69909 : int) (_69911 : int) : (term524 _69909 _69910 _69911) = (term308 _69909 _69911).
Proof. exact (MK_COMB (@lem5416922 _69910 _69909 _69911) (@lem5416923)). Qed.
Lemma lem5416925 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term308 _69909 _69911.
Proof. exact (EQ_MP (@lem5416924 _69910 _69909 _69911) (@lem5416673 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416927 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5416928 : term410 = term245.
Proof. exact (@lem5416927 term153 term170). Qed.
Lemma lem5416930 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416931 : term170 = term237.
Proof. exact (@lem5416930 term69). Qed.
Lemma lem5416933 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5416934 : term153 = term211.
Proof. exact (@lem5416933 (NUMERAL 0)). Qed.
Lemma lem5416935 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5416936 : term411 = term412.
Proof. exact (MK_COMB (@lem5416935) (@lem5416934)). Qed.
Lemma lem5416937 : term245 = term413.
Proof. exact (MK_COMB (@lem5416936) (@lem5416931)). Qed.
Lemma lem5416938 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5416940 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416941 : term245 = term246.
Proof. exact (@lem5416940 (NUMERAL 0) term69). Qed.
Lemma lem5416942 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416943 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416944 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416943 h1) (fun h1 : term246 = True => @lem5416942)). Qed.
Lemma lem5416945 : term246 = True.
Proof. exact (EQ_MP (@lem5416944) (@lem5416942)). Qed.
Lemma lem5416946 : term245 = True.
Proof. exact (TRANS (@lem5416941) (@lem5416945)). Qed.
Lemma lem5416947 : True = term245.
Proof. exact (SYM (@lem5416946)). Qed.
Lemma lem5416948 : term245.
Proof. exact (EQ_MP (@lem5416947) (@lem0)). Qed.
Lemma lem5416949 : term415.
Proof. exact (@lem5416938 (@lem5416948)). Qed.
Lemma lem5416951 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416952 : term245 = term246.
Proof. exact (@lem5416951 (NUMERAL 0) term69). Qed.
Lemma lem5416953 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416954 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416955 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416954 h1) (fun h1 : term246 = True => @lem5416953)). Qed.
Lemma lem5416956 : term246 = True.
Proof. exact (EQ_MP (@lem5416955) (@lem5416953)). Qed.
Lemma lem5416957 : term245 = True.
Proof. exact (TRANS (@lem5416952) (@lem5416956)). Qed.
Lemma lem5416958 : True = term245.
Proof. exact (SYM (@lem5416957)). Qed.
Lemma lem5416959 : term245.
Proof. exact (EQ_MP (@lem5416958) (@lem0)). Qed.
Lemma lem5416960 : term413 = term416.
Proof. exact (@lem5416949 (@lem5416959)). Qed.
Lemma lem5416962 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5416963 : term223 = term224.
Proof. exact (@lem5416962 term69 term69). Qed.
Lemma lem5416964 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5416965 : term226 = term69.
Proof. exact (EQ_MP (@lem5416964) (@lem940073)). Qed.
Lemma lem5416966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5416967 : term224 = term170.
Proof. exact (MK_COMB (@lem5416966) (@lem5416965)). Qed.
Lemma lem5416968 : term223 = term170.
Proof. exact (TRANS (@lem5416963) (@lem5416967)). Qed.
Lemma lem5416970 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5416971 : term418 = term153.
Proof. exact (@lem5416970 term69). Qed.
Lemma lem5416972 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5416973 : term419 = term411.
Proof. exact (MK_COMB (@lem5416972) (@lem5416971)). Qed.
Lemma lem5416974 : term416 = term245.
Proof. exact (MK_COMB (@lem5416973) (@lem5416968)). Qed.
Lemma lem5416976 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5416977 : term245 = term246.
Proof. exact (@lem5416976 (NUMERAL 0) term69). Qed.
Lemma lem5416978 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5416979 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5416980 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5416979 h1) (fun h1 : term246 = True => @lem5416978)). Qed.
Lemma lem5416981 : term246 = True.
Proof. exact (EQ_MP (@lem5416980) (@lem5416978)). Qed.
Lemma lem5416982 : term245 = True.
Proof. exact (TRANS (@lem5416977) (@lem5416981)). Qed.
Lemma lem5416983 : term416 = True.
Proof. exact (TRANS (@lem5416974) (@lem5416982)). Qed.
Lemma lem5416984 : term413 = True.
Proof. exact (TRANS (@lem5416960) (@lem5416983)). Qed.
Lemma lem5416985 : term245 = True.
Proof. exact (TRANS (@lem5416937) (@lem5416984)). Qed.
Lemma lem5416986 : term410 = True.
Proof. exact (TRANS (@lem5416928) (@lem5416985)). Qed.
Lemma lem5416987 : True = term410.
Proof. exact (SYM (@lem5416986)). Qed.
Lemma lem5416988 : term410.
Proof. exact (EQ_MP (@lem5416987) (@lem0)). Qed.
Lemma lem5416989 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term549 _69909 _69911.
Proof. exact (conj (@lem5416988) (@lem5416925 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416991 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5416992 (_69909 : int) (_69911 : int) : term550 _69909 _69911.
Proof. exact (@lem5416991 term170 (term305 _69909 _69911)). Qed.
Lemma lem5416993 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term551 _69909 _69911.
Proof. exact (@lem5416992 _69909 _69911 (@lem5416989 _69910 _69909 _69911 h1)). Qed.
Lemma lem5416994 (_69909 : int) (_69911 : int) : (term552 _69909 _69911) = (term305 _69909 _69911).
Proof. exact (@lem1982733 (term305 _69909 _69911)). Qed.
Lemma lem5416995 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5416996 (_69909 : int) (_69911 : int) : (term553 _69909 _69911) = (term307 _69909 _69911).
Proof. exact (MK_COMB (@lem5416995) (@lem5416994 _69909 _69911)). Qed.
Lemma lem5416997 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5416998 (_69909 : int) (_69911 : int) : (term551 _69909 _69911) = (term308 _69909 _69911).
Proof. exact (MK_COMB (@lem5416996 _69909 _69911) (@lem5416997)). Qed.
Lemma lem5416999 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term308 _69909 _69911.
Proof. exact (EQ_MP (@lem5416998 _69909 _69911) (@lem5416993 _69910 _69909 _69911 h1)). Qed.
Lemma lem5417001 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5417002 : term410 = term245.
Proof. exact (@lem5417001 term153 term170). Qed.
Lemma lem5417004 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417005 : term170 = term237.
Proof. exact (@lem5417004 term69). Qed.
Lemma lem5417007 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417008 : term153 = term211.
Proof. exact (@lem5417007 (NUMERAL 0)). Qed.
Lemma lem5417009 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417010 : term411 = term412.
Proof. exact (MK_COMB (@lem5417009) (@lem5417008)). Qed.
Lemma lem5417011 : term245 = term413.
Proof. exact (MK_COMB (@lem5417010) (@lem5417005)). Qed.
Lemma lem5417012 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5417014 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417015 : term245 = term246.
Proof. exact (@lem5417014 (NUMERAL 0) term69). Qed.
Lemma lem5417016 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417017 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417018 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417017 h1) (fun h1 : term246 = True => @lem5417016)). Qed.
Lemma lem5417019 : term246 = True.
Proof. exact (EQ_MP (@lem5417018) (@lem5417016)). Qed.
Lemma lem5417020 : term245 = True.
Proof. exact (TRANS (@lem5417015) (@lem5417019)). Qed.
Lemma lem5417021 : True = term245.
Proof. exact (SYM (@lem5417020)). Qed.
Lemma lem5417022 : term245.
Proof. exact (EQ_MP (@lem5417021) (@lem0)). Qed.
Lemma lem5417023 : term415.
Proof. exact (@lem5417012 (@lem5417022)). Qed.
Lemma lem5417025 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417026 : term245 = term246.
Proof. exact (@lem5417025 (NUMERAL 0) term69). Qed.
Lemma lem5417027 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417028 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417029 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417028 h1) (fun h1 : term246 = True => @lem5417027)). Qed.
Lemma lem5417030 : term246 = True.
Proof. exact (EQ_MP (@lem5417029) (@lem5417027)). Qed.
Lemma lem5417031 : term245 = True.
Proof. exact (TRANS (@lem5417026) (@lem5417030)). Qed.
Lemma lem5417032 : True = term245.
Proof. exact (SYM (@lem5417031)). Qed.
Lemma lem5417033 : term245.
Proof. exact (EQ_MP (@lem5417032) (@lem0)). Qed.
Lemma lem5417034 : term413 = term416.
Proof. exact (@lem5417023 (@lem5417033)). Qed.
Lemma lem5417036 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417037 : term223 = term224.
Proof. exact (@lem5417036 term69 term69). Qed.
Lemma lem5417038 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417039 : term226 = term69.
Proof. exact (EQ_MP (@lem5417038) (@lem940073)). Qed.
Lemma lem5417040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417041 : term224 = term170.
Proof. exact (MK_COMB (@lem5417040) (@lem5417039)). Qed.
Lemma lem5417042 : term223 = term170.
Proof. exact (TRANS (@lem5417037) (@lem5417041)). Qed.
Lemma lem5417044 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417045 : term418 = term153.
Proof. exact (@lem5417044 term69). Qed.
Lemma lem5417046 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417047 : term419 = term411.
Proof. exact (MK_COMB (@lem5417046) (@lem5417045)). Qed.
Lemma lem5417048 : term416 = term245.
Proof. exact (MK_COMB (@lem5417047) (@lem5417042)). Qed.
Lemma lem5417050 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417051 : term245 = term246.
Proof. exact (@lem5417050 (NUMERAL 0) term69). Qed.
Lemma lem5417052 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417053 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417054 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417053 h1) (fun h1 : term246 = True => @lem5417052)). Qed.
Lemma lem5417055 : term246 = True.
Proof. exact (EQ_MP (@lem5417054) (@lem5417052)). Qed.
Lemma lem5417056 : term245 = True.
Proof. exact (TRANS (@lem5417051) (@lem5417055)). Qed.
Lemma lem5417057 : term416 = True.
Proof. exact (TRANS (@lem5417048) (@lem5417056)). Qed.
Lemma lem5417058 : term413 = True.
Proof. exact (TRANS (@lem5417034) (@lem5417057)). Qed.
Lemma lem5417059 : term245 = True.
Proof. exact (TRANS (@lem5417011) (@lem5417058)). Qed.
Lemma lem5417060 : term410 = True.
Proof. exact (TRANS (@lem5417002) (@lem5417059)). Qed.
Lemma lem5417061 : True = term410.
Proof. exact (SYM (@lem5417060)). Qed.
Lemma lem5417062 : term410.
Proof. exact (EQ_MP (@lem5417061) (@lem0)). Qed.
Lemma lem5417063 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term463 _69909 _69911.
Proof. exact (conj (@lem5417062) (@lem5416520 _69910 _69909 _69911 h1)). Qed.
Lemma lem5417065 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5417066 (_69909 : int) (_69911 : int) : term464 _69909 _69911.
Proof. exact (@lem5417065 term170 (term318 _69909 _69911)). Qed.
Lemma lem5417067 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term465 _69909 _69911.
Proof. exact (@lem5417066 _69909 _69911 (@lem5417063 _69910 _69909 _69911 h1)). Qed.
Lemma lem5417068 (_69909 : int) (_69911 : int) : (term466 _69909 _69911) = (term318 _69909 _69911).
Proof. exact (@lem1982733 (term318 _69909 _69911)). Qed.
Lemma lem5417069 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5417070 (_69909 : int) (_69911 : int) : (term467 _69909 _69911) = (term320 _69909 _69911).
Proof. exact (MK_COMB (@lem5417069) (@lem5417068 _69909 _69911)). Qed.
Lemma lem5417071 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5417072 (_69909 : int) (_69911 : int) : (term465 _69909 _69911) = (term321 _69909 _69911).
Proof. exact (MK_COMB (@lem5417070 _69909 _69911) (@lem5417071)). Qed.
Lemma lem5417073 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term321 _69909 _69911.
Proof. exact (EQ_MP (@lem5417072 _69909 _69911) (@lem5417067 _69910 _69909 _69911 h1)). Qed.
Lemma lem5417074 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term554 _69909 _69911.
Proof. exact (conj (@lem5417073 _69910 _69909 _69911 h1) (@lem5416999 _69910 _69909 _69911 h1)). Qed.
Lemma lem5417076 (x : real) (y : real) : term432 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5417077 (_69909 : int) (_69911 : int) : term555 _69909 _69911.
Proof. exact (@lem5417076 (term318 _69909 _69911) (term305 _69909 _69911)). Qed.
Lemma lem5417078 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term556 _69909 _69911.
Proof. exact (@lem5417077 _69909 _69911 (@lem5417074 _69910 _69909 _69911 h1)). Qed.
Lemma lem5417079 (_69909 : int) (_69911 : int) : (term557 _69909 _69911) = (term558 _69909 _69911).
Proof. exact (@lem1982753 (term310 _69909) (real_of_int _69909) (real_of_int _69911) (term304 _69911)). Qed.
Lemma lem5417080 (_69909 : int) : (term439 _69909) = (term440 _69909).
Proof. exact (@lem1982713 term214 (real_of_int _69909)). Qed.
Lemma lem5417082 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417083 : term170 = term237.
Proof. exact (@lem5417082 term69). Qed.
Lemma lem5417085 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5417086 : term214 = term215.
Proof. exact (@lem5417085 term69). Qed.
Lemma lem5417087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417088 : term441 = term442.
Proof. exact (MK_COMB (@lem5417087) (@lem5417086)). Qed.
Lemma lem5417089 : term443 = term444.
Proof. exact (MK_COMB (@lem5417088) (@lem5417083)). Qed.
Lemma lem5417090 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5417092 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417093 : term245 = term246.
Proof. exact (@lem5417092 (NUMERAL 0) term69). Qed.
Lemma lem5417094 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417095 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417096 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417095 h1) (fun h1 : term246 = True => @lem5417094)). Qed.
Lemma lem5417097 : term246 = True.
Proof. exact (EQ_MP (@lem5417096) (@lem5417094)). Qed.
Lemma lem5417098 : term245 = True.
Proof. exact (TRANS (@lem5417093) (@lem5417097)). Qed.
Lemma lem5417099 : True = term245.
Proof. exact (SYM (@lem5417098)). Qed.
Lemma lem5417100 : term245.
Proof. exact (EQ_MP (@lem5417099) (@lem0)). Qed.
Lemma lem5417101 : term446.
Proof. exact (@lem5417090 (@lem5417100)). Qed.
Lemma lem5417103 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417104 : term245 = term246.
Proof. exact (@lem5417103 (NUMERAL 0) term69). Qed.
Lemma lem5417105 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417106 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417107 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417106 h1) (fun h1 : term246 = True => @lem5417105)). Qed.
Lemma lem5417108 : term246 = True.
Proof. exact (EQ_MP (@lem5417107) (@lem5417105)). Qed.
Lemma lem5417109 : term245 = True.
Proof. exact (TRANS (@lem5417104) (@lem5417108)). Qed.
Lemma lem5417110 : True = term245.
Proof. exact (SYM (@lem5417109)). Qed.
Lemma lem5417111 : term245.
Proof. exact (EQ_MP (@lem5417110) (@lem0)). Qed.
Lemma lem5417112 : term447.
Proof. exact (@lem5417101 (@lem5417111)). Qed.
Lemma lem5417114 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417115 : term245 = term246.
Proof. exact (@lem5417114 (NUMERAL 0) term69). Qed.
Lemma lem5417116 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417117 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417118 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417117 h1) (fun h1 : term246 = True => @lem5417116)). Qed.
Lemma lem5417119 : term246 = True.
Proof. exact (EQ_MP (@lem5417118) (@lem5417116)). Qed.
Lemma lem5417120 : term245 = True.
Proof. exact (TRANS (@lem5417115) (@lem5417119)). Qed.
Lemma lem5417121 : True = term245.
Proof. exact (SYM (@lem5417120)). Qed.
Lemma lem5417122 : term245.
Proof. exact (EQ_MP (@lem5417121) (@lem0)). Qed.
Lemma lem5417123 : term448.
Proof. exact (@lem5417112 (@lem5417122)). Qed.
Lemma lem5417125 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417126 : term223 = term224.
Proof. exact (@lem5417125 term69 term69). Qed.
Lemma lem5417127 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417128 : term226 = term69.
Proof. exact (EQ_MP (@lem5417127) (@lem940073)). Qed.
Lemma lem5417129 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417130 : term224 = term170.
Proof. exact (MK_COMB (@lem5417129) (@lem5417128)). Qed.
Lemma lem5417131 : term223 = term170.
Proof. exact (TRANS (@lem5417126) (@lem5417130)). Qed.
Lemma lem5417133 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5417134 : term298 = term301.
Proof. exact (@lem5417133 term69 term69). Qed.
Lemma lem5417135 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417136 : term226 = term69.
Proof. exact (EQ_MP (@lem5417135) (@lem940073)). Qed.
Lemma lem5417137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417138 : term224 = term170.
Proof. exact (MK_COMB (@lem5417137) (@lem5417136)). Qed.
Lemma lem5417139 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5417140 : term301 = term214.
Proof. exact (MK_COMB (@lem5417139) (@lem5417138)). Qed.
Lemma lem5417141 : term298 = term214.
Proof. exact (TRANS (@lem5417134) (@lem5417140)). Qed.
Lemma lem5417142 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417143 : term449 = term441.
Proof. exact (MK_COMB (@lem5417142) (@lem5417141)). Qed.
Lemma lem5417144 : term450 = term443.
Proof. exact (MK_COMB (@lem5417143) (@lem5417131)). Qed.
Lemma lem5417146 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5417147 : term443 = term153.
Proof. exact (@lem5417146 term69). Qed.
Lemma lem5417148 : term450 = term153.
Proof. exact (TRANS (@lem5417144) (@lem5417147)). Qed.
Lemma lem5417149 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5417150 : term452 = term453.
Proof. exact (MK_COMB (@lem5417149) (@lem5417148)). Qed.
Lemma lem5417151 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5417152 : term454 = term418.
Proof. exact (MK_COMB (@lem5417150) (@lem5417151)). Qed.
Lemma lem5417154 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417155 : term418 = term153.
Proof. exact (@lem5417154 term69). Qed.
Lemma lem5417156 : term454 = term153.
Proof. exact (TRANS (@lem5417152) (@lem5417155)). Qed.
Lemma lem5417158 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417159 : term223 = term224.
Proof. exact (@lem5417158 term69 term69). Qed.
Lemma lem5417160 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417161 : term226 = term69.
Proof. exact (EQ_MP (@lem5417160) (@lem940073)). Qed.
Lemma lem5417162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417163 : term224 = term170.
Proof. exact (MK_COMB (@lem5417162) (@lem5417161)). Qed.
Lemma lem5417164 : term223 = term170.
Proof. exact (TRANS (@lem5417159) (@lem5417163)). Qed.
Lemma lem5417165 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5417166 : term455 = term418.
Proof. exact (MK_COMB (@lem5417165) (@lem5417164)). Qed.
Lemma lem5417168 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417169 : term418 = term153.
Proof. exact (@lem5417168 term69). Qed.
Lemma lem5417170 : term455 = term153.
Proof. exact (TRANS (@lem5417166) (@lem5417169)). Qed.
Lemma lem5417171 : term153 = term455.
Proof. exact (SYM (@lem5417170)). Qed.
Lemma lem5417172 : term454 = term455.
Proof. exact (TRANS (@lem5417156) (@lem5417171)). Qed.
Lemma lem5417173 : term444 = term211.
Proof. exact (@lem5417123 (@lem5417172)). Qed.
Lemma lem5417174 : term443 = term211.
Proof. exact (TRANS (@lem5417089) (@lem5417173)). Qed.
Lemma lem5417176 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5417177 : term211 = term153.
Proof. exact (@lem5417176 term153). Qed.
Lemma lem5417178 : term443 = term153.
Proof. exact (TRANS (@lem5417174) (@lem5417177)). Qed.
Lemma lem5417179 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5417180 : term456 = term453.
Proof. exact (MK_COMB (@lem5417179) (@lem5417178)). Qed.
Lemma lem5417181 (_69909 : int) : (real_of_int _69909) = (real_of_int _69909).
Proof. exact (eq_refl (real_of_int _69909)). Qed.
Lemma lem5417182 (_69909 : int) : (term440 _69909) = (term457 _69909).
Proof. exact (MK_COMB (@lem5417180) (@lem5417181 _69909)). Qed.
Lemma lem5417183 (_69909 : int) : (term439 _69909) = (term457 _69909).
Proof. exact (TRANS (@lem5417080 _69909) (@lem5417182 _69909)). Qed.
Lemma lem5417184 (_69909 : int) : (term457 _69909) = term153.
Proof. exact (@lem1982719 (real_of_int _69909)). Qed.
Lemma lem5417185 (_69909 : int) : (term439 _69909) = term153.
Proof. exact (TRANS (@lem5417183 _69909) (@lem5417184 _69909)). Qed.
Lemma lem5417186 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417187 (_69909 : int) : (term458 _69909) = term459.
Proof. exact (MK_COMB (@lem5417186) (@lem5417185 _69909)). Qed.
Lemma lem5417188 (_69911 : int) : (term559 _69911) = (term560 _69911).
Proof. exact (@lem1982763 (real_of_int _69911) (term310 _69911) term214). Qed.
Lemma lem5417189 (_69911 : int) : (term475 _69911) = (term440 _69911).
Proof. exact (@lem1982715 term214 (real_of_int _69911)). Qed.
Lemma lem5417191 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417192 : term170 = term237.
Proof. exact (@lem5417191 term69). Qed.
Lemma lem5417194 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5417195 : term214 = term215.
Proof. exact (@lem5417194 term69). Qed.
Lemma lem5417196 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417197 : term441 = term442.
Proof. exact (MK_COMB (@lem5417196) (@lem5417195)). Qed.
Lemma lem5417198 : term443 = term444.
Proof. exact (MK_COMB (@lem5417197) (@lem5417192)). Qed.
Lemma lem5417199 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5417201 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417202 : term245 = term246.
Proof. exact (@lem5417201 (NUMERAL 0) term69). Qed.
Lemma lem5417203 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417204 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417205 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417204 h1) (fun h1 : term246 = True => @lem5417203)). Qed.
Lemma lem5417206 : term246 = True.
Proof. exact (EQ_MP (@lem5417205) (@lem5417203)). Qed.
Lemma lem5417207 : term245 = True.
Proof. exact (TRANS (@lem5417202) (@lem5417206)). Qed.
Lemma lem5417208 : True = term245.
Proof. exact (SYM (@lem5417207)). Qed.
Lemma lem5417209 : term245.
Proof. exact (EQ_MP (@lem5417208) (@lem0)). Qed.
Lemma lem5417210 : term446.
Proof. exact (@lem5417199 (@lem5417209)). Qed.
Lemma lem5417212 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417213 : term245 = term246.
Proof. exact (@lem5417212 (NUMERAL 0) term69). Qed.
Lemma lem5417214 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417215 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417216 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417215 h1) (fun h1 : term246 = True => @lem5417214)). Qed.
Lemma lem5417217 : term246 = True.
Proof. exact (EQ_MP (@lem5417216) (@lem5417214)). Qed.
Lemma lem5417218 : term245 = True.
Proof. exact (TRANS (@lem5417213) (@lem5417217)). Qed.
Lemma lem5417219 : True = term245.
Proof. exact (SYM (@lem5417218)). Qed.
Lemma lem5417220 : term245.
Proof. exact (EQ_MP (@lem5417219) (@lem0)). Qed.
Lemma lem5417221 : term447.
Proof. exact (@lem5417210 (@lem5417220)). Qed.
Lemma lem5417223 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417224 : term245 = term246.
Proof. exact (@lem5417223 (NUMERAL 0) term69). Qed.
Lemma lem5417225 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417226 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417227 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417226 h1) (fun h1 : term246 = True => @lem5417225)). Qed.
Lemma lem5417228 : term246 = True.
Proof. exact (EQ_MP (@lem5417227) (@lem5417225)). Qed.
Lemma lem5417229 : term245 = True.
Proof. exact (TRANS (@lem5417224) (@lem5417228)). Qed.
Lemma lem5417230 : True = term245.
Proof. exact (SYM (@lem5417229)). Qed.
Lemma lem5417231 : term245.
Proof. exact (EQ_MP (@lem5417230) (@lem0)). Qed.
Lemma lem5417232 : term448.
Proof. exact (@lem5417221 (@lem5417231)). Qed.
Lemma lem5417234 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417235 : term223 = term224.
Proof. exact (@lem5417234 term69 term69). Qed.
Lemma lem5417236 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417237 : term226 = term69.
Proof. exact (EQ_MP (@lem5417236) (@lem940073)). Qed.
Lemma lem5417238 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417239 : term224 = term170.
Proof. exact (MK_COMB (@lem5417238) (@lem5417237)). Qed.
Lemma lem5417240 : term223 = term170.
Proof. exact (TRANS (@lem5417235) (@lem5417239)). Qed.
Lemma lem5417242 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5417243 : term298 = term301.
Proof. exact (@lem5417242 term69 term69). Qed.
Lemma lem5417244 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417245 : term226 = term69.
Proof. exact (EQ_MP (@lem5417244) (@lem940073)). Qed.
Lemma lem5417246 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417247 : term224 = term170.
Proof. exact (MK_COMB (@lem5417246) (@lem5417245)). Qed.
Lemma lem5417248 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5417249 : term301 = term214.
Proof. exact (MK_COMB (@lem5417248) (@lem5417247)). Qed.
Lemma lem5417250 : term298 = term214.
Proof. exact (TRANS (@lem5417243) (@lem5417249)). Qed.
Lemma lem5417251 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417252 : term449 = term441.
Proof. exact (MK_COMB (@lem5417251) (@lem5417250)). Qed.
Lemma lem5417253 : term450 = term443.
Proof. exact (MK_COMB (@lem5417252) (@lem5417240)). Qed.
Lemma lem5417255 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5417256 : term443 = term153.
Proof. exact (@lem5417255 term69). Qed.
Lemma lem5417257 : term450 = term153.
Proof. exact (TRANS (@lem5417253) (@lem5417256)). Qed.
Lemma lem5417258 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5417259 : term452 = term453.
Proof. exact (MK_COMB (@lem5417258) (@lem5417257)). Qed.
Lemma lem5417260 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5417261 : term454 = term418.
Proof. exact (MK_COMB (@lem5417259) (@lem5417260)). Qed.
Lemma lem5417263 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417264 : term418 = term153.
Proof. exact (@lem5417263 term69). Qed.
Lemma lem5417265 : term454 = term153.
Proof. exact (TRANS (@lem5417261) (@lem5417264)). Qed.
Lemma lem5417267 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417268 : term223 = term224.
Proof. exact (@lem5417267 term69 term69). Qed.
Lemma lem5417269 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417270 : term226 = term69.
Proof. exact (EQ_MP (@lem5417269) (@lem940073)). Qed.
Lemma lem5417271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417272 : term224 = term170.
Proof. exact (MK_COMB (@lem5417271) (@lem5417270)). Qed.
Lemma lem5417273 : term223 = term170.
Proof. exact (TRANS (@lem5417268) (@lem5417272)). Qed.
Lemma lem5417274 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5417275 : term455 = term418.
Proof. exact (MK_COMB (@lem5417274) (@lem5417273)). Qed.
Lemma lem5417277 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417278 : term418 = term153.
Proof. exact (@lem5417277 term69). Qed.
Lemma lem5417279 : term455 = term153.
Proof. exact (TRANS (@lem5417275) (@lem5417278)). Qed.
Lemma lem5417280 : term153 = term455.
Proof. exact (SYM (@lem5417279)). Qed.
Lemma lem5417281 : term454 = term455.
Proof. exact (TRANS (@lem5417265) (@lem5417280)). Qed.
Lemma lem5417282 : term444 = term211.
Proof. exact (@lem5417232 (@lem5417281)). Qed.
Lemma lem5417283 : term443 = term211.
Proof. exact (TRANS (@lem5417198) (@lem5417282)). Qed.
Lemma lem5417285 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5417286 : term211 = term153.
Proof. exact (@lem5417285 term153). Qed.
Lemma lem5417287 : term443 = term153.
Proof. exact (TRANS (@lem5417283) (@lem5417286)). Qed.
Lemma lem5417288 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5417289 : term456 = term453.
Proof. exact (MK_COMB (@lem5417288) (@lem5417287)). Qed.
Lemma lem5417290 (_69911 : int) : (real_of_int _69911) = (real_of_int _69911).
Proof. exact (eq_refl (real_of_int _69911)). Qed.
Lemma lem5417291 (_69911 : int) : (term440 _69911) = (term457 _69911).
Proof. exact (MK_COMB (@lem5417289) (@lem5417290 _69911)). Qed.
Lemma lem5417292 (_69911 : int) : (term475 _69911) = (term457 _69911).
Proof. exact (TRANS (@lem5417189 _69911) (@lem5417291 _69911)). Qed.
Lemma lem5417293 (_69911 : int) : (term457 _69911) = term153.
Proof. exact (@lem1982719 (real_of_int _69911)). Qed.
Lemma lem5417294 (_69911 : int) : (term475 _69911) = term153.
Proof. exact (TRANS (@lem5417292 _69911) (@lem5417293 _69911)). Qed.
Lemma lem5417295 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417296 (_69911 : int) : (term476 _69911) = term459.
Proof. exact (MK_COMB (@lem5417295) (@lem5417294 _69911)). Qed.
Lemma lem5417297 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem5417298 (_69911 : int) : (term560 _69911) = term561.
Proof. exact (MK_COMB (@lem5417296 _69911) (@lem5417297)). Qed.
Lemma lem5417299 (_69911 : int) : (term559 _69911) = term561.
Proof. exact (TRANS (@lem5417188 _69911) (@lem5417298 _69911)). Qed.
Lemma lem5417300 : term561 = term214.
Proof. exact (@lem1982721 term214). Qed.
Lemma lem5417301 (_69911 : int) : (term559 _69911) = term214.
Proof. exact (TRANS (@lem5417299 _69911) (@lem5417300)). Qed.
Lemma lem5417302 (_69909 : int) (_69911 : int) : (term558 _69909 _69911) = term561.
Proof. exact (MK_COMB (@lem5417187 _69909) (@lem5417301 _69911)). Qed.
Lemma lem5417303 (_69909 : int) (_69911 : int) : (term557 _69909 _69911) = term561.
Proof. exact (TRANS (@lem5417079 _69909 _69911) (@lem5417302 _69909 _69911)). Qed.
Lemma lem5417304 : term561 = term214.
Proof. exact (@lem1982721 term214). Qed.
Lemma lem5417305 (_69909 : int) (_69911 : int) : (term557 _69909 _69911) = term214.
Proof. exact (TRANS (@lem5417303 _69909 _69911) (@lem5417304)). Qed.
Lemma lem5417306 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5417307 (_69909 : int) (_69911 : int) : (term562 _69909 _69911) = term563.
Proof. exact (MK_COMB (@lem5417306) (@lem5417305 _69909 _69911)). Qed.
Lemma lem5417308 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5417309 (_69909 : int) (_69911 : int) : (term556 _69909 _69911) = term564.
Proof. exact (MK_COMB (@lem5417307 _69909 _69911) (@lem5417308)). Qed.
Lemma lem5417310 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : term564.
Proof. exact (EQ_MP (@lem5417309 _69909 _69911) (@lem5417078 _69910 _69909 _69911 h1)). Qed.
Lemma lem5417312 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5417313 : term564 = term565.
Proof. exact (@lem5417312 term153 term214). Qed.
Lemma lem5417315 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5417316 : term214 = term215.
Proof. exact (@lem5417315 term69). Qed.
Lemma lem5417318 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417319 : term153 = term211.
Proof. exact (@lem5417318 (NUMERAL 0)). Qed.
Lemma lem5417320 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5417321 : term155 = term482.
Proof. exact (MK_COMB (@lem5417320) (@lem5417319)). Qed.
Lemma lem5417322 : term565 = term566.
Proof. exact (MK_COMB (@lem5417321) (@lem5417316)). Qed.
Lemma lem5417323 : term567.
Proof. exact (@lem1980026 term153 term170 term214 term170). Qed.
Lemma lem5417325 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417326 : term245 = term246.
Proof. exact (@lem5417325 (NUMERAL 0) term69). Qed.
Lemma lem5417327 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417328 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417329 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417328 h1) (fun h1 : term246 = True => @lem5417327)). Qed.
Lemma lem5417330 : term246 = True.
Proof. exact (EQ_MP (@lem5417329) (@lem5417327)). Qed.
Lemma lem5417331 : term245 = True.
Proof. exact (TRANS (@lem5417326) (@lem5417330)). Qed.
Lemma lem5417332 : True = term245.
Proof. exact (SYM (@lem5417331)). Qed.
Lemma lem5417333 : term245.
Proof. exact (EQ_MP (@lem5417332) (@lem0)). Qed.
Lemma lem5417334 : term568.
Proof. exact (@lem5417323 (@lem5417333)). Qed.
Lemma lem5417336 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417337 : term245 = term246.
Proof. exact (@lem5417336 (NUMERAL 0) term69). Qed.
Lemma lem5417338 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417339 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417340 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417339 h1) (fun h1 : term246 = True => @lem5417338)). Qed.
Lemma lem5417341 : term246 = True.
Proof. exact (EQ_MP (@lem5417340) (@lem5417338)). Qed.
Lemma lem5417342 : term245 = True.
Proof. exact (TRANS (@lem5417337) (@lem5417341)). Qed.
Lemma lem5417343 : True = term245.
Proof. exact (SYM (@lem5417342)). Qed.
Lemma lem5417344 : term245.
Proof. exact (EQ_MP (@lem5417343) (@lem0)). Qed.
Lemma lem5417345 : term566 = term569.
Proof. exact (@lem5417334 (@lem5417344)). Qed.
Lemma lem5417347 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5417348 : term298 = term301.
Proof. exact (@lem5417347 term69 term69). Qed.
Lemma lem5417349 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417350 : term226 = term69.
Proof. exact (EQ_MP (@lem5417349) (@lem940073)). Qed.
Lemma lem5417351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417352 : term224 = term170.
Proof. exact (MK_COMB (@lem5417351) (@lem5417350)). Qed.
Lemma lem5417353 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5417354 : term301 = term214.
Proof. exact (MK_COMB (@lem5417353) (@lem5417352)). Qed.
Lemma lem5417355 : term298 = term214.
Proof. exact (TRANS (@lem5417348) (@lem5417354)). Qed.
Lemma lem5417357 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417358 : term418 = term153.
Proof. exact (@lem5417357 term69). Qed.
Lemma lem5417359 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5417360 : term489 = term155.
Proof. exact (MK_COMB (@lem5417359) (@lem5417358)). Qed.
Lemma lem5417361 : term569 = term565.
Proof. exact (MK_COMB (@lem5417360) (@lem5417355)). Qed.
Lemma lem5417363 (m : nat) (n : nat) : (term490 m n) = (term491 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5417364 : term565 = term570.
Proof. exact (@lem5417363 (NUMERAL 0) term69). Qed.
Lemma lem5417365 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417366 (h1 : term247 = (BIT1 0)) : (term69 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5417367 : (term247 = (BIT1 0)) = ((term69 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417366 h1) (fun h1 : (term69 = (NUMERAL 0)) = False => @lem5417365)). Qed.
Lemma lem5417368 : (term69 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5417367) (@lem5417365)). Qed.
Lemma lem5417369 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5417370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5417371 : term494 = (and True).
Proof. exact (MK_COMB (@lem5417370) (@lem5417369)). Qed.
Lemma lem5417372 : term570 = (True /\ False).
Proof. exact (MK_COMB (@lem5417371) (@lem5417368)). Qed.
Lemma lem5417374 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5417375 : term570 = False.
Proof. exact (TRANS (@lem5417372) (@lem5417374)). Qed.
Lemma lem5417376 : term565 = False.
Proof. exact (TRANS (@lem5417364) (@lem5417375)). Qed.
Lemma lem5417377 : term569 = False.
Proof. exact (TRANS (@lem5417361) (@lem5417376)). Qed.
Lemma lem5417378 : term566 = False.
Proof. exact (TRANS (@lem5417345) (@lem5417377)). Qed.
Lemma lem5417379 : term565 = False.
Proof. exact (TRANS (@lem5417322) (@lem5417378)). Qed.
Lemma lem5417380 : term564 = False.
Proof. exact (TRANS (@lem5417313) (@lem5417379)). Qed.
Lemma lem5417381 (_69910 : int) (_69909 : int) (_69911 : int) (h1 : term516 _69910 _69909 _69911) : False.
Proof. exact (EQ_MP (@lem5417380) (@lem5417310 _69910 _69909 _69911 h1)). Qed.
Lemma lem5417382 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term571 _69909 _69910 _69911.
Proof. exact (h1). Qed.
Lemma lem5417383 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term401 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5417382 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417385 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term388 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5417383 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417387 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term375 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5417385 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417389 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term362 _69909 _69910 _69911.
Proof. exact (proj2 (@lem5417387 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417390 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term292 _69909 _69910.
Proof. exact (proj1 (@lem5417387 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417392 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term338 _69909 _69910 _69911.
Proof. exact (proj1 (@lem5417389 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417393 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term337 _69910 _69911.
Proof. exact (proj2 (@lem5417392 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417394 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term321 _69909 _69911.
Proof. exact (proj1 (@lem5417392 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417396 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5417397 : term410 = term245.
Proof. exact (@lem5417396 term153 term170). Qed.
Lemma lem5417399 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417400 : term170 = term237.
Proof. exact (@lem5417399 term69). Qed.
Lemma lem5417402 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417403 : term153 = term211.
Proof. exact (@lem5417402 (NUMERAL 0)). Qed.
Lemma lem5417404 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417405 : term411 = term412.
Proof. exact (MK_COMB (@lem5417404) (@lem5417403)). Qed.
Lemma lem5417406 : term245 = term413.
Proof. exact (MK_COMB (@lem5417405) (@lem5417400)). Qed.
Lemma lem5417407 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5417409 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417410 : term245 = term246.
Proof. exact (@lem5417409 (NUMERAL 0) term69). Qed.
Lemma lem5417411 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417412 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417413 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417412 h1) (fun h1 : term246 = True => @lem5417411)). Qed.
Lemma lem5417414 : term246 = True.
Proof. exact (EQ_MP (@lem5417413) (@lem5417411)). Qed.
Lemma lem5417415 : term245 = True.
Proof. exact (TRANS (@lem5417410) (@lem5417414)). Qed.
Lemma lem5417416 : True = term245.
Proof. exact (SYM (@lem5417415)). Qed.
Lemma lem5417417 : term245.
Proof. exact (EQ_MP (@lem5417416) (@lem0)). Qed.
Lemma lem5417418 : term415.
Proof. exact (@lem5417407 (@lem5417417)). Qed.
Lemma lem5417420 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417421 : term245 = term246.
Proof. exact (@lem5417420 (NUMERAL 0) term69). Qed.
Lemma lem5417422 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417423 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417424 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417423 h1) (fun h1 : term246 = True => @lem5417422)). Qed.
Lemma lem5417425 : term246 = True.
Proof. exact (EQ_MP (@lem5417424) (@lem5417422)). Qed.
Lemma lem5417426 : term245 = True.
Proof. exact (TRANS (@lem5417421) (@lem5417425)). Qed.
Lemma lem5417427 : True = term245.
Proof. exact (SYM (@lem5417426)). Qed.
Lemma lem5417428 : term245.
Proof. exact (EQ_MP (@lem5417427) (@lem0)). Qed.
Lemma lem5417429 : term413 = term416.
Proof. exact (@lem5417418 (@lem5417428)). Qed.
Lemma lem5417431 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417432 : term223 = term224.
Proof. exact (@lem5417431 term69 term69). Qed.
Lemma lem5417433 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417434 : term226 = term69.
Proof. exact (EQ_MP (@lem5417433) (@lem940073)). Qed.
Lemma lem5417435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417436 : term224 = term170.
Proof. exact (MK_COMB (@lem5417435) (@lem5417434)). Qed.
Lemma lem5417437 : term223 = term170.
Proof. exact (TRANS (@lem5417432) (@lem5417436)). Qed.
Lemma lem5417439 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417440 : term418 = term153.
Proof. exact (@lem5417439 term69). Qed.
Lemma lem5417441 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417442 : term419 = term411.
Proof. exact (MK_COMB (@lem5417441) (@lem5417440)). Qed.
Lemma lem5417443 : term416 = term245.
Proof. exact (MK_COMB (@lem5417442) (@lem5417437)). Qed.
Lemma lem5417445 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417446 : term245 = term246.
Proof. exact (@lem5417445 (NUMERAL 0) term69). Qed.
Lemma lem5417447 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417448 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417449 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417448 h1) (fun h1 : term246 = True => @lem5417447)). Qed.
Lemma lem5417450 : term246 = True.
Proof. exact (EQ_MP (@lem5417449) (@lem5417447)). Qed.
Lemma lem5417451 : term245 = True.
Proof. exact (TRANS (@lem5417446) (@lem5417450)). Qed.
Lemma lem5417452 : term416 = True.
Proof. exact (TRANS (@lem5417443) (@lem5417451)). Qed.
Lemma lem5417453 : term413 = True.
Proof. exact (TRANS (@lem5417429) (@lem5417452)). Qed.
Lemma lem5417454 : term245 = True.
Proof. exact (TRANS (@lem5417406) (@lem5417453)). Qed.
Lemma lem5417455 : term410 = True.
Proof. exact (TRANS (@lem5417397) (@lem5417454)). Qed.
Lemma lem5417456 : True = term410.
Proof. exact (SYM (@lem5417455)). Qed.
Lemma lem5417457 : term410.
Proof. exact (EQ_MP (@lem5417456) (@lem0)). Qed.
Lemma lem5417458 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term517 _69910 _69911.
Proof. exact (conj (@lem5417457) (@lem5417393 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417460 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5417461 (_69910 : int) (_69911 : int) : term518 _69910 _69911.
Proof. exact (@lem5417460 term170 (term334 _69910 _69911)). Qed.
Lemma lem5417462 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term519 _69910 _69911.
Proof. exact (@lem5417461 _69910 _69911 (@lem5417458 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417463 (_69910 : int) (_69911 : int) : (term520 _69910 _69911) = (term334 _69910 _69911).
Proof. exact (@lem1982733 (term334 _69910 _69911)). Qed.
Lemma lem5417464 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5417465 (_69910 : int) (_69911 : int) : (term521 _69910 _69911) = (term336 _69910 _69911).
Proof. exact (MK_COMB (@lem5417464) (@lem5417463 _69910 _69911)). Qed.
Lemma lem5417466 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5417467 (_69910 : int) (_69911 : int) : (term519 _69910 _69911) = (term337 _69910 _69911).
Proof. exact (MK_COMB (@lem5417465 _69910 _69911) (@lem5417466)). Qed.
Lemma lem5417468 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term337 _69910 _69911.
Proof. exact (EQ_MP (@lem5417467 _69910 _69911) (@lem5417462 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417470 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5417471 : term410 = term245.
Proof. exact (@lem5417470 term153 term170). Qed.
Lemma lem5417473 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417474 : term170 = term237.
Proof. exact (@lem5417473 term69). Qed.
Lemma lem5417476 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417477 : term153 = term211.
Proof. exact (@lem5417476 (NUMERAL 0)). Qed.
Lemma lem5417478 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417479 : term411 = term412.
Proof. exact (MK_COMB (@lem5417478) (@lem5417477)). Qed.
Lemma lem5417480 : term245 = term413.
Proof. exact (MK_COMB (@lem5417479) (@lem5417474)). Qed.
Lemma lem5417481 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5417483 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417484 : term245 = term246.
Proof. exact (@lem5417483 (NUMERAL 0) term69). Qed.
Lemma lem5417485 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417486 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417487 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417486 h1) (fun h1 : term246 = True => @lem5417485)). Qed.
Lemma lem5417488 : term246 = True.
Proof. exact (EQ_MP (@lem5417487) (@lem5417485)). Qed.
Lemma lem5417489 : term245 = True.
Proof. exact (TRANS (@lem5417484) (@lem5417488)). Qed.
Lemma lem5417490 : True = term245.
Proof. exact (SYM (@lem5417489)). Qed.
Lemma lem5417491 : term245.
Proof. exact (EQ_MP (@lem5417490) (@lem0)). Qed.
Lemma lem5417492 : term415.
Proof. exact (@lem5417481 (@lem5417491)). Qed.
Lemma lem5417494 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417495 : term245 = term246.
Proof. exact (@lem5417494 (NUMERAL 0) term69). Qed.
Lemma lem5417496 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417497 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417498 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417497 h1) (fun h1 : term246 = True => @lem5417496)). Qed.
Lemma lem5417499 : term246 = True.
Proof. exact (EQ_MP (@lem5417498) (@lem5417496)). Qed.
Lemma lem5417500 : term245 = True.
Proof. exact (TRANS (@lem5417495) (@lem5417499)). Qed.
Lemma lem5417501 : True = term245.
Proof. exact (SYM (@lem5417500)). Qed.
Lemma lem5417502 : term245.
Proof. exact (EQ_MP (@lem5417501) (@lem0)). Qed.
Lemma lem5417503 : term413 = term416.
Proof. exact (@lem5417492 (@lem5417502)). Qed.
Lemma lem5417505 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417506 : term223 = term224.
Proof. exact (@lem5417505 term69 term69). Qed.
Lemma lem5417507 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417508 : term226 = term69.
Proof. exact (EQ_MP (@lem5417507) (@lem940073)). Qed.
Lemma lem5417509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417510 : term224 = term170.
Proof. exact (MK_COMB (@lem5417509) (@lem5417508)). Qed.
Lemma lem5417511 : term223 = term170.
Proof. exact (TRANS (@lem5417506) (@lem5417510)). Qed.
Lemma lem5417513 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417514 : term418 = term153.
Proof. exact (@lem5417513 term69). Qed.
Lemma lem5417515 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417516 : term419 = term411.
Proof. exact (MK_COMB (@lem5417515) (@lem5417514)). Qed.
Lemma lem5417517 : term416 = term245.
Proof. exact (MK_COMB (@lem5417516) (@lem5417511)). Qed.
Lemma lem5417519 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417520 : term245 = term246.
Proof. exact (@lem5417519 (NUMERAL 0) term69). Qed.
Lemma lem5417521 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417522 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417523 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417522 h1) (fun h1 : term246 = True => @lem5417521)). Qed.
Lemma lem5417524 : term246 = True.
Proof. exact (EQ_MP (@lem5417523) (@lem5417521)). Qed.
Lemma lem5417525 : term245 = True.
Proof. exact (TRANS (@lem5417520) (@lem5417524)). Qed.
Lemma lem5417526 : term416 = True.
Proof. exact (TRANS (@lem5417517) (@lem5417525)). Qed.
Lemma lem5417527 : term413 = True.
Proof. exact (TRANS (@lem5417503) (@lem5417526)). Qed.
Lemma lem5417528 : term245 = True.
Proof. exact (TRANS (@lem5417480) (@lem5417527)). Qed.
Lemma lem5417529 : term410 = True.
Proof. exact (TRANS (@lem5417471) (@lem5417528)). Qed.
Lemma lem5417530 : True = term410.
Proof. exact (SYM (@lem5417529)). Qed.
Lemma lem5417531 : term410.
Proof. exact (EQ_MP (@lem5417530) (@lem0)). Qed.
Lemma lem5417532 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term426 _69909 _69910.
Proof. exact (conj (@lem5417531) (@lem5417390 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417534 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5417535 (_69909 : int) (_69910 : int) : term427 _69909 _69910.
Proof. exact (@lem5417534 term170 (term289 _69909 _69910)). Qed.
Lemma lem5417536 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term428 _69909 _69910.
Proof. exact (@lem5417535 _69909 _69910 (@lem5417532 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417537 (_69909 : int) (_69910 : int) : (term429 _69909 _69910) = (term289 _69909 _69910).
Proof. exact (@lem1982733 (term289 _69909 _69910)). Qed.
Lemma lem5417538 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5417539 (_69909 : int) (_69910 : int) : (term430 _69909 _69910) = (term291 _69909 _69910).
Proof. exact (MK_COMB (@lem5417538) (@lem5417537 _69909 _69910)). Qed.
Lemma lem5417540 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5417541 (_69909 : int) (_69910 : int) : (term428 _69909 _69910) = (term292 _69909 _69910).
Proof. exact (MK_COMB (@lem5417539 _69909 _69910) (@lem5417540)). Qed.
Lemma lem5417542 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term292 _69909 _69910.
Proof. exact (EQ_MP (@lem5417541 _69909 _69910) (@lem5417536 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417544 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5417545 : term410 = term245.
Proof. exact (@lem5417544 term153 term170). Qed.
Lemma lem5417547 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417548 : term170 = term237.
Proof. exact (@lem5417547 term69). Qed.
Lemma lem5417550 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417551 : term153 = term211.
Proof. exact (@lem5417550 (NUMERAL 0)). Qed.
Lemma lem5417552 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417553 : term411 = term412.
Proof. exact (MK_COMB (@lem5417552) (@lem5417551)). Qed.
Lemma lem5417554 : term245 = term413.
Proof. exact (MK_COMB (@lem5417553) (@lem5417548)). Qed.
Lemma lem5417555 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5417557 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417558 : term245 = term246.
Proof. exact (@lem5417557 (NUMERAL 0) term69). Qed.
Lemma lem5417559 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417560 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417561 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417560 h1) (fun h1 : term246 = True => @lem5417559)). Qed.
Lemma lem5417562 : term246 = True.
Proof. exact (EQ_MP (@lem5417561) (@lem5417559)). Qed.
Lemma lem5417563 : term245 = True.
Proof. exact (TRANS (@lem5417558) (@lem5417562)). Qed.
Lemma lem5417564 : True = term245.
Proof. exact (SYM (@lem5417563)). Qed.
Lemma lem5417565 : term245.
Proof. exact (EQ_MP (@lem5417564) (@lem0)). Qed.
Lemma lem5417566 : term415.
Proof. exact (@lem5417555 (@lem5417565)). Qed.
Lemma lem5417568 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417569 : term245 = term246.
Proof. exact (@lem5417568 (NUMERAL 0) term69). Qed.
Lemma lem5417570 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417571 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417572 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417571 h1) (fun h1 : term246 = True => @lem5417570)). Qed.
Lemma lem5417573 : term246 = True.
Proof. exact (EQ_MP (@lem5417572) (@lem5417570)). Qed.
Lemma lem5417574 : term245 = True.
Proof. exact (TRANS (@lem5417569) (@lem5417573)). Qed.
Lemma lem5417575 : True = term245.
Proof. exact (SYM (@lem5417574)). Qed.
Lemma lem5417576 : term245.
Proof. exact (EQ_MP (@lem5417575) (@lem0)). Qed.
Lemma lem5417577 : term413 = term416.
Proof. exact (@lem5417566 (@lem5417576)). Qed.
Lemma lem5417579 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417580 : term223 = term224.
Proof. exact (@lem5417579 term69 term69). Qed.
Lemma lem5417581 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417582 : term226 = term69.
Proof. exact (EQ_MP (@lem5417581) (@lem940073)). Qed.
Lemma lem5417583 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417584 : term224 = term170.
Proof. exact (MK_COMB (@lem5417583) (@lem5417582)). Qed.
Lemma lem5417585 : term223 = term170.
Proof. exact (TRANS (@lem5417580) (@lem5417584)). Qed.
Lemma lem5417587 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417588 : term418 = term153.
Proof. exact (@lem5417587 term69). Qed.
Lemma lem5417589 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417590 : term419 = term411.
Proof. exact (MK_COMB (@lem5417589) (@lem5417588)). Qed.
Lemma lem5417591 : term416 = term245.
Proof. exact (MK_COMB (@lem5417590) (@lem5417585)). Qed.
Lemma lem5417593 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417594 : term245 = term246.
Proof. exact (@lem5417593 (NUMERAL 0) term69). Qed.
Lemma lem5417595 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417596 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417597 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417596 h1) (fun h1 : term246 = True => @lem5417595)). Qed.
Lemma lem5417598 : term246 = True.
Proof. exact (EQ_MP (@lem5417597) (@lem5417595)). Qed.
Lemma lem5417599 : term245 = True.
Proof. exact (TRANS (@lem5417594) (@lem5417598)). Qed.
Lemma lem5417600 : term416 = True.
Proof. exact (TRANS (@lem5417591) (@lem5417599)). Qed.
Lemma lem5417601 : term413 = True.
Proof. exact (TRANS (@lem5417577) (@lem5417600)). Qed.
Lemma lem5417602 : term245 = True.
Proof. exact (TRANS (@lem5417554) (@lem5417601)). Qed.
Lemma lem5417603 : term410 = True.
Proof. exact (TRANS (@lem5417545) (@lem5417602)). Qed.
Lemma lem5417604 : True = term410.
Proof. exact (SYM (@lem5417603)). Qed.
Lemma lem5417605 : term410.
Proof. exact (EQ_MP (@lem5417604) (@lem0)). Qed.
Lemma lem5417606 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term463 _69909 _69911.
Proof. exact (conj (@lem5417605) (@lem5417394 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417608 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5417609 (_69909 : int) (_69911 : int) : term464 _69909 _69911.
Proof. exact (@lem5417608 term170 (term318 _69909 _69911)). Qed.
Lemma lem5417610 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term465 _69909 _69911.
Proof. exact (@lem5417609 _69909 _69911 (@lem5417606 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417611 (_69909 : int) (_69911 : int) : (term466 _69909 _69911) = (term318 _69909 _69911).
Proof. exact (@lem1982733 (term318 _69909 _69911)). Qed.
Lemma lem5417612 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5417613 (_69909 : int) (_69911 : int) : (term467 _69909 _69911) = (term320 _69909 _69911).
Proof. exact (MK_COMB (@lem5417612) (@lem5417611 _69909 _69911)). Qed.
Lemma lem5417614 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5417615 (_69909 : int) (_69911 : int) : (term465 _69909 _69911) = (term321 _69909 _69911).
Proof. exact (MK_COMB (@lem5417613 _69909 _69911) (@lem5417614)). Qed.
Lemma lem5417616 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term321 _69909 _69911.
Proof. exact (EQ_MP (@lem5417615 _69909 _69911) (@lem5417610 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417617 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term496 _69911 _69909 _69910.
Proof. exact (conj (@lem5417616 _69909 _69910 _69911 h1) (@lem5417542 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417619 (x : real) (y : real) : term432 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5417620 (_69911 : int) (_69909 : int) (_69910 : int) : term497 _69911 _69909 _69910.
Proof. exact (@lem5417619 (term318 _69909 _69911) (term289 _69909 _69910)). Qed.
Lemma lem5417621 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term498 _69911 _69909 _69910.
Proof. exact (@lem5417620 _69911 _69909 _69910 (@lem5417617 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417622 (_69909 : int) (_69911 : int) (_69910 : int) : (term499 _69911 _69909 _69910) = (term500 _69909 _69911 _69910).
Proof. exact (@lem1982753 (term310 _69909) (real_of_int _69909) (real_of_int _69911) (term288 _69910)). Qed.
Lemma lem5417623 (_69909 : int) : (term439 _69909) = (term440 _69909).
Proof. exact (@lem1982713 term214 (real_of_int _69909)). Qed.
Lemma lem5417625 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417626 : term170 = term237.
Proof. exact (@lem5417625 term69). Qed.
Lemma lem5417628 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5417629 : term214 = term215.
Proof. exact (@lem5417628 term69). Qed.
Lemma lem5417630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417631 : term441 = term442.
Proof. exact (MK_COMB (@lem5417630) (@lem5417629)). Qed.
Lemma lem5417632 : term443 = term444.
Proof. exact (MK_COMB (@lem5417631) (@lem5417626)). Qed.
Lemma lem5417633 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5417635 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417636 : term245 = term246.
Proof. exact (@lem5417635 (NUMERAL 0) term69). Qed.
Lemma lem5417637 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417638 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417639 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417638 h1) (fun h1 : term246 = True => @lem5417637)). Qed.
Lemma lem5417640 : term246 = True.
Proof. exact (EQ_MP (@lem5417639) (@lem5417637)). Qed.
Lemma lem5417641 : term245 = True.
Proof. exact (TRANS (@lem5417636) (@lem5417640)). Qed.
Lemma lem5417642 : True = term245.
Proof. exact (SYM (@lem5417641)). Qed.
Lemma lem5417643 : term245.
Proof. exact (EQ_MP (@lem5417642) (@lem0)). Qed.
Lemma lem5417644 : term446.
Proof. exact (@lem5417633 (@lem5417643)). Qed.
Lemma lem5417646 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417647 : term245 = term246.
Proof. exact (@lem5417646 (NUMERAL 0) term69). Qed.
Lemma lem5417648 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417649 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417650 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417649 h1) (fun h1 : term246 = True => @lem5417648)). Qed.
Lemma lem5417651 : term246 = True.
Proof. exact (EQ_MP (@lem5417650) (@lem5417648)). Qed.
Lemma lem5417652 : term245 = True.
Proof. exact (TRANS (@lem5417647) (@lem5417651)). Qed.
Lemma lem5417653 : True = term245.
Proof. exact (SYM (@lem5417652)). Qed.
Lemma lem5417654 : term245.
Proof. exact (EQ_MP (@lem5417653) (@lem0)). Qed.
Lemma lem5417655 : term447.
Proof. exact (@lem5417644 (@lem5417654)). Qed.
Lemma lem5417657 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417658 : term245 = term246.
Proof. exact (@lem5417657 (NUMERAL 0) term69). Qed.
Lemma lem5417659 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417660 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417661 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417660 h1) (fun h1 : term246 = True => @lem5417659)). Qed.
Lemma lem5417662 : term246 = True.
Proof. exact (EQ_MP (@lem5417661) (@lem5417659)). Qed.
Lemma lem5417663 : term245 = True.
Proof. exact (TRANS (@lem5417658) (@lem5417662)). Qed.
Lemma lem5417664 : True = term245.
Proof. exact (SYM (@lem5417663)). Qed.
Lemma lem5417665 : term245.
Proof. exact (EQ_MP (@lem5417664) (@lem0)). Qed.
Lemma lem5417666 : term448.
Proof. exact (@lem5417655 (@lem5417665)). Qed.
Lemma lem5417668 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417669 : term223 = term224.
Proof. exact (@lem5417668 term69 term69). Qed.
Lemma lem5417670 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417671 : term226 = term69.
Proof. exact (EQ_MP (@lem5417670) (@lem940073)). Qed.
Lemma lem5417672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417673 : term224 = term170.
Proof. exact (MK_COMB (@lem5417672) (@lem5417671)). Qed.
Lemma lem5417674 : term223 = term170.
Proof. exact (TRANS (@lem5417669) (@lem5417673)). Qed.
Lemma lem5417676 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5417677 : term298 = term301.
Proof. exact (@lem5417676 term69 term69). Qed.
Lemma lem5417678 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417679 : term226 = term69.
Proof. exact (EQ_MP (@lem5417678) (@lem940073)). Qed.
Lemma lem5417680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417681 : term224 = term170.
Proof. exact (MK_COMB (@lem5417680) (@lem5417679)). Qed.
Lemma lem5417682 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5417683 : term301 = term214.
Proof. exact (MK_COMB (@lem5417682) (@lem5417681)). Qed.
Lemma lem5417684 : term298 = term214.
Proof. exact (TRANS (@lem5417677) (@lem5417683)). Qed.
Lemma lem5417685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417686 : term449 = term441.
Proof. exact (MK_COMB (@lem5417685) (@lem5417684)). Qed.
Lemma lem5417687 : term450 = term443.
Proof. exact (MK_COMB (@lem5417686) (@lem5417674)). Qed.
Lemma lem5417689 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5417690 : term443 = term153.
Proof. exact (@lem5417689 term69). Qed.
Lemma lem5417691 : term450 = term153.
Proof. exact (TRANS (@lem5417687) (@lem5417690)). Qed.
Lemma lem5417692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5417693 : term452 = term453.
Proof. exact (MK_COMB (@lem5417692) (@lem5417691)). Qed.
Lemma lem5417694 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5417695 : term454 = term418.
Proof. exact (MK_COMB (@lem5417693) (@lem5417694)). Qed.
Lemma lem5417697 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417698 : term418 = term153.
Proof. exact (@lem5417697 term69). Qed.
Lemma lem5417699 : term454 = term153.
Proof. exact (TRANS (@lem5417695) (@lem5417698)). Qed.
Lemma lem5417701 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417702 : term223 = term224.
Proof. exact (@lem5417701 term69 term69). Qed.
Lemma lem5417703 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417704 : term226 = term69.
Proof. exact (EQ_MP (@lem5417703) (@lem940073)). Qed.
Lemma lem5417705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417706 : term224 = term170.
Proof. exact (MK_COMB (@lem5417705) (@lem5417704)). Qed.
Lemma lem5417707 : term223 = term170.
Proof. exact (TRANS (@lem5417702) (@lem5417706)). Qed.
Lemma lem5417708 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5417709 : term455 = term418.
Proof. exact (MK_COMB (@lem5417708) (@lem5417707)). Qed.
Lemma lem5417711 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417712 : term418 = term153.
Proof. exact (@lem5417711 term69). Qed.
Lemma lem5417713 : term455 = term153.
Proof. exact (TRANS (@lem5417709) (@lem5417712)). Qed.
Lemma lem5417714 : term153 = term455.
Proof. exact (SYM (@lem5417713)). Qed.
Lemma lem5417715 : term454 = term455.
Proof. exact (TRANS (@lem5417699) (@lem5417714)). Qed.
Lemma lem5417716 : term444 = term211.
Proof. exact (@lem5417666 (@lem5417715)). Qed.
Lemma lem5417717 : term443 = term211.
Proof. exact (TRANS (@lem5417632) (@lem5417716)). Qed.
Lemma lem5417719 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5417720 : term211 = term153.
Proof. exact (@lem5417719 term153). Qed.
Lemma lem5417721 : term443 = term153.
Proof. exact (TRANS (@lem5417717) (@lem5417720)). Qed.
Lemma lem5417722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5417723 : term456 = term453.
Proof. exact (MK_COMB (@lem5417722) (@lem5417721)). Qed.
Lemma lem5417724 (_69909 : int) : (real_of_int _69909) = (real_of_int _69909).
Proof. exact (eq_refl (real_of_int _69909)). Qed.
Lemma lem5417725 (_69909 : int) : (term440 _69909) = (term457 _69909).
Proof. exact (MK_COMB (@lem5417723) (@lem5417724 _69909)). Qed.
Lemma lem5417726 (_69909 : int) : (term439 _69909) = (term457 _69909).
Proof. exact (TRANS (@lem5417623 _69909) (@lem5417725 _69909)). Qed.
Lemma lem5417727 (_69909 : int) : (term457 _69909) = term153.
Proof. exact (@lem1982719 (real_of_int _69909)). Qed.
Lemma lem5417728 (_69909 : int) : (term439 _69909) = term153.
Proof. exact (TRANS (@lem5417726 _69909) (@lem5417727 _69909)). Qed.
Lemma lem5417729 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417730 (_69909 : int) : (term458 _69909) = term459.
Proof. exact (MK_COMB (@lem5417729) (@lem5417728 _69909)). Qed.
Lemma lem5417735 (_69910 : int) (_69911 : int) : (term289 _69911 _69910) = (term309 _69910 _69911).
Proof. exact (@lem1982757 (term310 _69910) (real_of_int _69911) term283). Qed.
Lemma lem5417736 (_69909 : int) (_69910 : int) (_69911 : int) : (term500 _69909 _69911 _69910) = (term501 _69910 _69911).
Proof. exact (MK_COMB (@lem5417730 _69909) (@lem5417735 _69910 _69911)). Qed.
Lemma lem5417737 (_69909 : int) (_69910 : int) (_69911 : int) : (term499 _69911 _69909 _69910) = (term501 _69910 _69911).
Proof. exact (TRANS (@lem5417622 _69909 _69911 _69910) (@lem5417736 _69909 _69910 _69911)). Qed.
Lemma lem5417738 (_69910 : int) (_69911 : int) : (term501 _69910 _69911) = (term309 _69910 _69911).
Proof. exact (@lem1982721 (term309 _69910 _69911)). Qed.
Lemma lem5417739 (_69909 : int) (_69910 : int) (_69911 : int) : (term499 _69911 _69909 _69910) = (term309 _69910 _69911).
Proof. exact (TRANS (@lem5417737 _69909 _69910 _69911) (@lem5417738 _69910 _69911)). Qed.
Lemma lem5417740 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5417741 (_69909 : int) (_69910 : int) (_69911 : int) : (term502 _69911 _69909 _69910) = (term311 _69910 _69911).
Proof. exact (MK_COMB (@lem5417740) (@lem5417739 _69909 _69910 _69911)). Qed.
Lemma lem5417742 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5417743 (_69909 : int) (_69910 : int) (_69911 : int) : (term498 _69911 _69909 _69910) = (term312 _69910 _69911).
Proof. exact (MK_COMB (@lem5417741 _69909 _69910 _69911) (@lem5417742)). Qed.
Lemma lem5417744 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term312 _69910 _69911.
Proof. exact (EQ_MP (@lem5417743 _69909 _69910 _69911) (@lem5417621 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417746 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5417747 : term410 = term245.
Proof. exact (@lem5417746 term153 term170). Qed.
Lemma lem5417749 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417750 : term170 = term237.
Proof. exact (@lem5417749 term69). Qed.
Lemma lem5417752 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417753 : term153 = term211.
Proof. exact (@lem5417752 (NUMERAL 0)). Qed.
Lemma lem5417754 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417755 : term411 = term412.
Proof. exact (MK_COMB (@lem5417754) (@lem5417753)). Qed.
Lemma lem5417756 : term245 = term413.
Proof. exact (MK_COMB (@lem5417755) (@lem5417750)). Qed.
Lemma lem5417757 : term414.
Proof. exact (@lem1980255 term153 term170 term170 term170). Qed.
Lemma lem5417759 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417760 : term245 = term246.
Proof. exact (@lem5417759 (NUMERAL 0) term69). Qed.
Lemma lem5417761 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417762 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417763 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417762 h1) (fun h1 : term246 = True => @lem5417761)). Qed.
Lemma lem5417764 : term246 = True.
Proof. exact (EQ_MP (@lem5417763) (@lem5417761)). Qed.
Lemma lem5417765 : term245 = True.
Proof. exact (TRANS (@lem5417760) (@lem5417764)). Qed.
Lemma lem5417766 : True = term245.
Proof. exact (SYM (@lem5417765)). Qed.
Lemma lem5417767 : term245.
Proof. exact (EQ_MP (@lem5417766) (@lem0)). Qed.
Lemma lem5417768 : term415.
Proof. exact (@lem5417757 (@lem5417767)). Qed.
Lemma lem5417770 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417771 : term245 = term246.
Proof. exact (@lem5417770 (NUMERAL 0) term69). Qed.
Lemma lem5417772 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417773 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417774 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417773 h1) (fun h1 : term246 = True => @lem5417772)). Qed.
Lemma lem5417775 : term246 = True.
Proof. exact (EQ_MP (@lem5417774) (@lem5417772)). Qed.
Lemma lem5417776 : term245 = True.
Proof. exact (TRANS (@lem5417771) (@lem5417775)). Qed.
Lemma lem5417777 : True = term245.
Proof. exact (SYM (@lem5417776)). Qed.
Lemma lem5417778 : term245.
Proof. exact (EQ_MP (@lem5417777) (@lem0)). Qed.
Lemma lem5417779 : term413 = term416.
Proof. exact (@lem5417768 (@lem5417778)). Qed.
Lemma lem5417781 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417782 : term223 = term224.
Proof. exact (@lem5417781 term69 term69). Qed.
Lemma lem5417783 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417784 : term226 = term69.
Proof. exact (EQ_MP (@lem5417783) (@lem940073)). Qed.
Lemma lem5417785 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417786 : term224 = term170.
Proof. exact (MK_COMB (@lem5417785) (@lem5417784)). Qed.
Lemma lem5417787 : term223 = term170.
Proof. exact (TRANS (@lem5417782) (@lem5417786)). Qed.
Lemma lem5417789 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417790 : term418 = term153.
Proof. exact (@lem5417789 term69). Qed.
Lemma lem5417791 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5417792 : term419 = term411.
Proof. exact (MK_COMB (@lem5417791) (@lem5417790)). Qed.
Lemma lem5417793 : term416 = term245.
Proof. exact (MK_COMB (@lem5417792) (@lem5417787)). Qed.
Lemma lem5417795 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417796 : term245 = term246.
Proof. exact (@lem5417795 (NUMERAL 0) term69). Qed.
Lemma lem5417797 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417798 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417799 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417798 h1) (fun h1 : term246 = True => @lem5417797)). Qed.
Lemma lem5417800 : term246 = True.
Proof. exact (EQ_MP (@lem5417799) (@lem5417797)). Qed.
Lemma lem5417801 : term245 = True.
Proof. exact (TRANS (@lem5417796) (@lem5417800)). Qed.
Lemma lem5417802 : term416 = True.
Proof. exact (TRANS (@lem5417793) (@lem5417801)). Qed.
Lemma lem5417803 : term413 = True.
Proof. exact (TRANS (@lem5417779) (@lem5417802)). Qed.
Lemma lem5417804 : term245 = True.
Proof. exact (TRANS (@lem5417756) (@lem5417803)). Qed.
Lemma lem5417805 : term410 = True.
Proof. exact (TRANS (@lem5417747) (@lem5417804)). Qed.
Lemma lem5417806 : True = term410.
Proof. exact (SYM (@lem5417805)). Qed.
Lemma lem5417807 : term410.
Proof. exact (EQ_MP (@lem5417806) (@lem0)). Qed.
Lemma lem5417808 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term503 _69910 _69911.
Proof. exact (conj (@lem5417807) (@lem5417744 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417810 (x : real) (y : real) : term421 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5417811 (_69910 : int) (_69911 : int) : term504 _69910 _69911.
Proof. exact (@lem5417810 term170 (term309 _69910 _69911)). Qed.
Lemma lem5417812 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term505 _69910 _69911.
Proof. exact (@lem5417811 _69910 _69911 (@lem5417808 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417813 (_69910 : int) (_69911 : int) : (term506 _69910 _69911) = (term309 _69910 _69911).
Proof. exact (@lem1982733 (term309 _69910 _69911)). Qed.
Lemma lem5417814 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5417815 (_69910 : int) (_69911 : int) : (term507 _69910 _69911) = (term311 _69910 _69911).
Proof. exact (MK_COMB (@lem5417814) (@lem5417813 _69910 _69911)). Qed.
Lemma lem5417816 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5417817 (_69910 : int) (_69911 : int) : (term505 _69910 _69911) = (term312 _69910 _69911).
Proof. exact (MK_COMB (@lem5417815 _69910 _69911) (@lem5417816)). Qed.
Lemma lem5417818 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term312 _69910 _69911.
Proof. exact (EQ_MP (@lem5417817 _69910 _69911) (@lem5417812 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417819 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term572 _69910 _69911.
Proof. exact (conj (@lem5417818 _69909 _69910 _69911 h1) (@lem5417468 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417821 (x : real) (y : real) : term432 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5417822 (_69910 : int) (_69911 : int) : term573 _69910 _69911.
Proof. exact (@lem5417821 (term309 _69910 _69911) (term334 _69910 _69911)). Qed.
Lemma lem5417823 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term574 _69910 _69911.
Proof. exact (@lem5417822 _69910 _69911 (@lem5417819 _69909 _69910 _69911 h1)). Qed.
Lemma lem5417824 (_69910 : int) (_69911 : int) : (term575 _69910 _69911) = (term576 _69910 _69911).
Proof. exact (@lem1982753 (term310 _69910) (real_of_int _69910) (term513 _69911) (term333 _69911)). Qed.
Lemma lem5417825 (_69910 : int) : (term439 _69910) = (term440 _69910).
Proof. exact (@lem1982713 term214 (real_of_int _69910)). Qed.
Lemma lem5417827 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417828 : term170 = term237.
Proof. exact (@lem5417827 term69). Qed.
Lemma lem5417830 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5417831 : term214 = term215.
Proof. exact (@lem5417830 term69). Qed.
Lemma lem5417832 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417833 : term441 = term442.
Proof. exact (MK_COMB (@lem5417832) (@lem5417831)). Qed.
Lemma lem5417834 : term443 = term444.
Proof. exact (MK_COMB (@lem5417833) (@lem5417828)). Qed.
Lemma lem5417835 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5417837 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417838 : term245 = term246.
Proof. exact (@lem5417837 (NUMERAL 0) term69). Qed.
Lemma lem5417839 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417840 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417841 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417840 h1) (fun h1 : term246 = True => @lem5417839)). Qed.
Lemma lem5417842 : term246 = True.
Proof. exact (EQ_MP (@lem5417841) (@lem5417839)). Qed.
Lemma lem5417843 : term245 = True.
Proof. exact (TRANS (@lem5417838) (@lem5417842)). Qed.
Lemma lem5417844 : True = term245.
Proof. exact (SYM (@lem5417843)). Qed.
Lemma lem5417845 : term245.
Proof. exact (EQ_MP (@lem5417844) (@lem0)). Qed.
Lemma lem5417846 : term446.
Proof. exact (@lem5417835 (@lem5417845)). Qed.
Lemma lem5417848 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417849 : term245 = term246.
Proof. exact (@lem5417848 (NUMERAL 0) term69). Qed.
Lemma lem5417850 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417851 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417852 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417851 h1) (fun h1 : term246 = True => @lem5417850)). Qed.
Lemma lem5417853 : term246 = True.
Proof. exact (EQ_MP (@lem5417852) (@lem5417850)). Qed.
Lemma lem5417854 : term245 = True.
Proof. exact (TRANS (@lem5417849) (@lem5417853)). Qed.
Lemma lem5417855 : True = term245.
Proof. exact (SYM (@lem5417854)). Qed.
Lemma lem5417856 : term245.
Proof. exact (EQ_MP (@lem5417855) (@lem0)). Qed.
Lemma lem5417857 : term447.
Proof. exact (@lem5417846 (@lem5417856)). Qed.
Lemma lem5417859 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417860 : term245 = term246.
Proof. exact (@lem5417859 (NUMERAL 0) term69). Qed.
Lemma lem5417861 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417862 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417863 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417862 h1) (fun h1 : term246 = True => @lem5417861)). Qed.
Lemma lem5417864 : term246 = True.
Proof. exact (EQ_MP (@lem5417863) (@lem5417861)). Qed.
Lemma lem5417865 : term245 = True.
Proof. exact (TRANS (@lem5417860) (@lem5417864)). Qed.
Lemma lem5417866 : True = term245.
Proof. exact (SYM (@lem5417865)). Qed.
Lemma lem5417867 : term245.
Proof. exact (EQ_MP (@lem5417866) (@lem0)). Qed.
Lemma lem5417868 : term448.
Proof. exact (@lem5417857 (@lem5417867)). Qed.
Lemma lem5417870 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417871 : term223 = term224.
Proof. exact (@lem5417870 term69 term69). Qed.
Lemma lem5417872 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417873 : term226 = term69.
Proof. exact (EQ_MP (@lem5417872) (@lem940073)). Qed.
Lemma lem5417874 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417875 : term224 = term170.
Proof. exact (MK_COMB (@lem5417874) (@lem5417873)). Qed.
Lemma lem5417876 : term223 = term170.
Proof. exact (TRANS (@lem5417871) (@lem5417875)). Qed.
Lemma lem5417878 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5417879 : term298 = term301.
Proof. exact (@lem5417878 term69 term69). Qed.
Lemma lem5417880 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417881 : term226 = term69.
Proof. exact (EQ_MP (@lem5417880) (@lem940073)). Qed.
Lemma lem5417882 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417883 : term224 = term170.
Proof. exact (MK_COMB (@lem5417882) (@lem5417881)). Qed.
Lemma lem5417884 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5417885 : term301 = term214.
Proof. exact (MK_COMB (@lem5417884) (@lem5417883)). Qed.
Lemma lem5417886 : term298 = term214.
Proof. exact (TRANS (@lem5417879) (@lem5417885)). Qed.
Lemma lem5417887 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417888 : term449 = term441.
Proof. exact (MK_COMB (@lem5417887) (@lem5417886)). Qed.
Lemma lem5417889 : term450 = term443.
Proof. exact (MK_COMB (@lem5417888) (@lem5417876)). Qed.
Lemma lem5417891 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5417892 : term443 = term153.
Proof. exact (@lem5417891 term69). Qed.
Lemma lem5417893 : term450 = term153.
Proof. exact (TRANS (@lem5417889) (@lem5417892)). Qed.
Lemma lem5417894 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5417895 : term452 = term453.
Proof. exact (MK_COMB (@lem5417894) (@lem5417893)). Qed.
Lemma lem5417896 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5417897 : term454 = term418.
Proof. exact (MK_COMB (@lem5417895) (@lem5417896)). Qed.
Lemma lem5417899 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417900 : term418 = term153.
Proof. exact (@lem5417899 term69). Qed.
Lemma lem5417901 : term454 = term153.
Proof. exact (TRANS (@lem5417897) (@lem5417900)). Qed.
Lemma lem5417903 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417904 : term223 = term224.
Proof. exact (@lem5417903 term69 term69). Qed.
Lemma lem5417905 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417906 : term226 = term69.
Proof. exact (EQ_MP (@lem5417905) (@lem940073)). Qed.
Lemma lem5417907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417908 : term224 = term170.
Proof. exact (MK_COMB (@lem5417907) (@lem5417906)). Qed.
Lemma lem5417909 : term223 = term170.
Proof. exact (TRANS (@lem5417904) (@lem5417908)). Qed.
Lemma lem5417910 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5417911 : term455 = term418.
Proof. exact (MK_COMB (@lem5417910) (@lem5417909)). Qed.
Lemma lem5417913 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5417914 : term418 = term153.
Proof. exact (@lem5417913 term69). Qed.
Lemma lem5417915 : term455 = term153.
Proof. exact (TRANS (@lem5417911) (@lem5417914)). Qed.
Lemma lem5417916 : term153 = term455.
Proof. exact (SYM (@lem5417915)). Qed.
Lemma lem5417917 : term454 = term455.
Proof. exact (TRANS (@lem5417901) (@lem5417916)). Qed.
Lemma lem5417918 : term444 = term211.
Proof. exact (@lem5417868 (@lem5417917)). Qed.
Lemma lem5417919 : term443 = term211.
Proof. exact (TRANS (@lem5417834) (@lem5417918)). Qed.
Lemma lem5417921 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5417922 : term211 = term153.
Proof. exact (@lem5417921 term153). Qed.
Lemma lem5417923 : term443 = term153.
Proof. exact (TRANS (@lem5417919) (@lem5417922)). Qed.
Lemma lem5417924 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5417925 : term456 = term453.
Proof. exact (MK_COMB (@lem5417924) (@lem5417923)). Qed.
Lemma lem5417926 (_69910 : int) : (real_of_int _69910) = (real_of_int _69910).
Proof. exact (eq_refl (real_of_int _69910)). Qed.
Lemma lem5417927 (_69910 : int) : (term440 _69910) = (term457 _69910).
Proof. exact (MK_COMB (@lem5417925) (@lem5417926 _69910)). Qed.
Lemma lem5417928 (_69910 : int) : (term439 _69910) = (term457 _69910).
Proof. exact (TRANS (@lem5417825 _69910) (@lem5417927 _69910)). Qed.
Lemma lem5417929 (_69910 : int) : (term457 _69910) = term153.
Proof. exact (@lem1982719 (real_of_int _69910)). Qed.
Lemma lem5417930 (_69910 : int) : (term439 _69910) = term153.
Proof. exact (TRANS (@lem5417928 _69910) (@lem5417929 _69910)). Qed.
Lemma lem5417931 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417932 (_69910 : int) : (term458 _69910) = term459.
Proof. exact (MK_COMB (@lem5417931) (@lem5417930 _69910)). Qed.
Lemma lem5417933 (_69911 : int) : (term577 _69911) = (term578 _69911).
Proof. exact (@lem1982753 (real_of_int _69911) (term310 _69911) term283 term170). Qed.
Lemma lem5417934 (_69911 : int) : (term475 _69911) = (term440 _69911).
Proof. exact (@lem1982715 term214 (real_of_int _69911)). Qed.
Lemma lem5417936 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5417937 : term170 = term237.
Proof. exact (@lem5417936 term69). Qed.
Lemma lem5417939 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5417940 : term214 = term215.
Proof. exact (@lem5417939 term69). Qed.
Lemma lem5417941 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417942 : term441 = term442.
Proof. exact (MK_COMB (@lem5417941) (@lem5417940)). Qed.
Lemma lem5417943 : term443 = term444.
Proof. exact (MK_COMB (@lem5417942) (@lem5417937)). Qed.
Lemma lem5417944 : term445.
Proof. exact (@lem1981473 term214 term170 term170 term170 term153 term170). Qed.
Lemma lem5417946 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417947 : term245 = term246.
Proof. exact (@lem5417946 (NUMERAL 0) term69). Qed.
Lemma lem5417948 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417949 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417950 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417949 h1) (fun h1 : term246 = True => @lem5417948)). Qed.
Lemma lem5417951 : term246 = True.
Proof. exact (EQ_MP (@lem5417950) (@lem5417948)). Qed.
Lemma lem5417952 : term245 = True.
Proof. exact (TRANS (@lem5417947) (@lem5417951)). Qed.
Lemma lem5417953 : True = term245.
Proof. exact (SYM (@lem5417952)). Qed.
Lemma lem5417954 : term245.
Proof. exact (EQ_MP (@lem5417953) (@lem0)). Qed.
Lemma lem5417955 : term446.
Proof. exact (@lem5417944 (@lem5417954)). Qed.
Lemma lem5417957 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417958 : term245 = term246.
Proof. exact (@lem5417957 (NUMERAL 0) term69). Qed.
Lemma lem5417959 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417960 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417961 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417960 h1) (fun h1 : term246 = True => @lem5417959)). Qed.
Lemma lem5417962 : term246 = True.
Proof. exact (EQ_MP (@lem5417961) (@lem5417959)). Qed.
Lemma lem5417963 : term245 = True.
Proof. exact (TRANS (@lem5417958) (@lem5417962)). Qed.
Lemma lem5417964 : True = term245.
Proof. exact (SYM (@lem5417963)). Qed.
Lemma lem5417965 : term245.
Proof. exact (EQ_MP (@lem5417964) (@lem0)). Qed.
Lemma lem5417966 : term447.
Proof. exact (@lem5417955 (@lem5417965)). Qed.
Lemma lem5417968 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5417969 : term245 = term246.
Proof. exact (@lem5417968 (NUMERAL 0) term69). Qed.
Lemma lem5417970 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5417971 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5417972 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5417971 h1) (fun h1 : term246 = True => @lem5417970)). Qed.
Lemma lem5417973 : term246 = True.
Proof. exact (EQ_MP (@lem5417972) (@lem5417970)). Qed.
Lemma lem5417974 : term245 = True.
Proof. exact (TRANS (@lem5417969) (@lem5417973)). Qed.
Lemma lem5417975 : True = term245.
Proof. exact (SYM (@lem5417974)). Qed.
Lemma lem5417976 : term245.
Proof. exact (EQ_MP (@lem5417975) (@lem0)). Qed.
Lemma lem5417977 : term448.
Proof. exact (@lem5417966 (@lem5417976)). Qed.
Lemma lem5417979 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5417980 : term223 = term224.
Proof. exact (@lem5417979 term69 term69). Qed.
Lemma lem5417981 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417982 : term226 = term69.
Proof. exact (EQ_MP (@lem5417981) (@lem940073)). Qed.
Lemma lem5417983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417984 : term224 = term170.
Proof. exact (MK_COMB (@lem5417983) (@lem5417982)). Qed.
Lemma lem5417985 : term223 = term170.
Proof. exact (TRANS (@lem5417980) (@lem5417984)). Qed.
Lemma lem5417987 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5417988 : term298 = term301.
Proof. exact (@lem5417987 term69 term69). Qed.
Lemma lem5417989 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5417990 : term226 = term69.
Proof. exact (EQ_MP (@lem5417989) (@lem940073)). Qed.
Lemma lem5417991 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5417992 : term224 = term170.
Proof. exact (MK_COMB (@lem5417991) (@lem5417990)). Qed.
Lemma lem5417993 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5417994 : term301 = term214.
Proof. exact (MK_COMB (@lem5417993) (@lem5417992)). Qed.
Lemma lem5417995 : term298 = term214.
Proof. exact (TRANS (@lem5417988) (@lem5417994)). Qed.
Lemma lem5417996 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5417997 : term449 = term441.
Proof. exact (MK_COMB (@lem5417996) (@lem5417995)). Qed.
Lemma lem5417998 : term450 = term443.
Proof. exact (MK_COMB (@lem5417997) (@lem5417985)). Qed.
Lemma lem5418000 (m : nat) : (term451 m) = term153.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5418001 : term443 = term153.
Proof. exact (@lem5418000 term69). Qed.
Lemma lem5418002 : term450 = term153.
Proof. exact (TRANS (@lem5417998) (@lem5418001)). Qed.
Lemma lem5418003 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5418004 : term452 = term453.
Proof. exact (MK_COMB (@lem5418003) (@lem5418002)). Qed.
Lemma lem5418005 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5418006 : term454 = term418.
Proof. exact (MK_COMB (@lem5418004) (@lem5418005)). Qed.
Lemma lem5418008 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5418009 : term418 = term153.
Proof. exact (@lem5418008 term69). Qed.
Lemma lem5418010 : term454 = term153.
Proof. exact (TRANS (@lem5418006) (@lem5418009)). Qed.
Lemma lem5418012 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5418013 : term223 = term224.
Proof. exact (@lem5418012 term69 term69). Qed.
Lemma lem5418014 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5418015 : term226 = term69.
Proof. exact (EQ_MP (@lem5418014) (@lem940073)). Qed.
Lemma lem5418016 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5418017 : term224 = term170.
Proof. exact (MK_COMB (@lem5418016) (@lem5418015)). Qed.
Lemma lem5418018 : term223 = term170.
Proof. exact (TRANS (@lem5418013) (@lem5418017)). Qed.
Lemma lem5418019 : term453 = term453.
Proof. exact (eq_refl term453). Qed.
Lemma lem5418020 : term455 = term418.
Proof. exact (MK_COMB (@lem5418019) (@lem5418018)). Qed.
Lemma lem5418022 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5418023 : term418 = term153.
Proof. exact (@lem5418022 term69). Qed.
Lemma lem5418024 : term455 = term153.
Proof. exact (TRANS (@lem5418020) (@lem5418023)). Qed.
Lemma lem5418025 : term153 = term455.
Proof. exact (SYM (@lem5418024)). Qed.
Lemma lem5418026 : term454 = term455.
Proof. exact (TRANS (@lem5418010) (@lem5418025)). Qed.
Lemma lem5418027 : term444 = term211.
Proof. exact (@lem5417977 (@lem5418026)). Qed.
Lemma lem5418028 : term443 = term211.
Proof. exact (TRANS (@lem5417943) (@lem5418027)). Qed.
Lemma lem5418030 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5418031 : term211 = term153.
Proof. exact (@lem5418030 term153). Qed.
Lemma lem5418032 : term443 = term153.
Proof. exact (TRANS (@lem5418028) (@lem5418031)). Qed.
Lemma lem5418033 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5418034 : term456 = term453.
Proof. exact (MK_COMB (@lem5418033) (@lem5418032)). Qed.
Lemma lem5418035 (_69911 : int) : (real_of_int _69911) = (real_of_int _69911).
Proof. exact (eq_refl (real_of_int _69911)). Qed.
Lemma lem5418036 (_69911 : int) : (term440 _69911) = (term457 _69911).
Proof. exact (MK_COMB (@lem5418034) (@lem5418035 _69911)). Qed.
Lemma lem5418037 (_69911 : int) : (term475 _69911) = (term457 _69911).
Proof. exact (TRANS (@lem5417934 _69911) (@lem5418036 _69911)). Qed.
Lemma lem5418038 (_69911 : int) : (term457 _69911) = term153.
Proof. exact (@lem1982719 (real_of_int _69911)). Qed.
Lemma lem5418039 (_69911 : int) : (term475 _69911) = term153.
Proof. exact (TRANS (@lem5418037 _69911) (@lem5418038 _69911)). Qed.
Lemma lem5418040 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5418041 (_69911 : int) : (term476 _69911) = term459.
Proof. exact (MK_COMB (@lem5418040) (@lem5418039 _69911)). Qed.
Lemma lem5418043 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5418044 : term170 = term237.
Proof. exact (@lem5418043 term69). Qed.
Lemma lem5418046 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5418047 : term283 = term286.
Proof. exact (@lem5418046 term257). Qed.
Lemma lem5418048 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5418049 : term531 = term532.
Proof. exact (MK_COMB (@lem5418048) (@lem5418047)). Qed.
Lemma lem5418050 : term533 = term534.
Proof. exact (MK_COMB (@lem5418049) (@lem5418044)). Qed.
Lemma lem5418051 : term535.
Proof. exact (@lem1981473 term283 term170 term170 term170 term214 term170). Qed.
Lemma lem5418053 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5418054 : term245 = term246.
Proof. exact (@lem5418053 (NUMERAL 0) term69). Qed.
Lemma lem5418055 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5418056 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5418057 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5418056 h1) (fun h1 : term246 = True => @lem5418055)). Qed.
Lemma lem5418058 : term246 = True.
Proof. exact (EQ_MP (@lem5418057) (@lem5418055)). Qed.
Lemma lem5418059 : term245 = True.
Proof. exact (TRANS (@lem5418054) (@lem5418058)). Qed.
Lemma lem5418060 : True = term245.
Proof. exact (SYM (@lem5418059)). Qed.
Lemma lem5418061 : term245.
Proof. exact (EQ_MP (@lem5418060) (@lem0)). Qed.
Lemma lem5418062 : term536.
Proof. exact (@lem5418051 (@lem5418061)). Qed.
Lemma lem5418064 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5418065 : term245 = term246.
Proof. exact (@lem5418064 (NUMERAL 0) term69). Qed.
Lemma lem5418066 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5418067 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5418068 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5418067 h1) (fun h1 : term246 = True => @lem5418066)). Qed.
Lemma lem5418069 : term246 = True.
Proof. exact (EQ_MP (@lem5418068) (@lem5418066)). Qed.
Lemma lem5418070 : term245 = True.
Proof. exact (TRANS (@lem5418065) (@lem5418069)). Qed.
Lemma lem5418071 : True = term245.
Proof. exact (SYM (@lem5418070)). Qed.
Lemma lem5418072 : term245.
Proof. exact (EQ_MP (@lem5418071) (@lem0)). Qed.
Lemma lem5418073 : term537.
Proof. exact (@lem5418062 (@lem5418072)). Qed.
Lemma lem5418075 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5418076 : term245 = term246.
Proof. exact (@lem5418075 (NUMERAL 0) term69). Qed.
Lemma lem5418077 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5418078 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5418079 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5418078 h1) (fun h1 : term246 = True => @lem5418077)). Qed.
Lemma lem5418080 : term246 = True.
Proof. exact (EQ_MP (@lem5418079) (@lem5418077)). Qed.
Lemma lem5418081 : term245 = True.
Proof. exact (TRANS (@lem5418076) (@lem5418080)). Qed.
Lemma lem5418082 : True = term245.
Proof. exact (SYM (@lem5418081)). Qed.
Lemma lem5418083 : term245.
Proof. exact (EQ_MP (@lem5418082) (@lem0)). Qed.
Lemma lem5418084 : term538.
Proof. exact (@lem5418073 (@lem5418083)). Qed.
Lemma lem5418086 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5418087 : term223 = term224.
Proof. exact (@lem5418086 term69 term69). Qed.
Lemma lem5418088 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5418089 : term226 = term69.
Proof. exact (EQ_MP (@lem5418088) (@lem940073)). Qed.
Lemma lem5418090 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5418091 : term224 = term170.
Proof. exact (MK_COMB (@lem5418090) (@lem5418089)). Qed.
Lemma lem5418092 : term223 = term170.
Proof. exact (TRANS (@lem5418087) (@lem5418091)). Qed.
Lemma lem5418094 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5418095 : term487 = term488.
Proof. exact (@lem5418094 term257 term69). Qed.
Lemma lem5418096 : term263 = term255.
Proof. exact (@lem996237 term255). Qed.
Lemma lem5418097 : (term263 = term255) = (term264 = term257).
Proof. exact (@lem1007663 term255 (BIT1 0) term255). Qed.
Lemma lem5418098 : term264 = term257.
Proof. exact (EQ_MP (@lem5418097) (@lem5418096)). Qed.
Lemma lem5418099 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5418100 : term262 = term243.
Proof. exact (MK_COMB (@lem5418099) (@lem5418098)). Qed.
Lemma lem5418101 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5418102 : term488 = term283.
Proof. exact (MK_COMB (@lem5418101) (@lem5418100)). Qed.
Lemma lem5418103 : term487 = term283.
Proof. exact (TRANS (@lem5418095) (@lem5418102)). Qed.
Lemma lem5418104 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5418105 : term539 = term531.
Proof. exact (MK_COMB (@lem5418104) (@lem5418103)). Qed.
Lemma lem5418106 : term540 = term533.
Proof. exact (MK_COMB (@lem5418105) (@lem5418092)). Qed.
Lemma lem5418109 : term541 = term214.
Proof. exact (@lem1367767 term69 term69). Qed.
Lemma lem5418110 : term254 = term255.
Proof. exact (@lem706885). Qed.
Lemma lem5418111 : (term254 = term255) = (term256 = term257).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term255). Qed.
Lemma lem5418112 : term256 = term257.
Proof. exact (EQ_MP (@lem5418111) (@lem5418110)). Qed.
Lemma lem5418113 : term257 = term256.
Proof. exact (SYM (@lem5418112)). Qed.
Lemma lem5418114 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5418115 : term243 = term253.
Proof. exact (MK_COMB (@lem5418114) (@lem5418113)). Qed.
Lemma lem5418116 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5418117 : term283 = term542.
Proof. exact (MK_COMB (@lem5418116) (@lem5418115)). Qed.
Lemma lem5418118 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5418119 : term531 = term543.
Proof. exact (MK_COMB (@lem5418118) (@lem5418117)). Qed.
Lemma lem5418120 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5418121 : term533 = term541.
Proof. exact (MK_COMB (@lem5418119) (@lem5418120)). Qed.
Lemma lem5418122 : term533 = term214.
Proof. exact (TRANS (@lem5418121) (@lem5418109)). Qed.
Lemma lem5418123 : term540 = term214.
Proof. exact (TRANS (@lem5418106) (@lem5418122)). Qed.
Lemma lem5418124 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5418125 : term544 = term216.
Proof. exact (MK_COMB (@lem5418124) (@lem5418123)). Qed.
Lemma lem5418126 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem5418127 : term545 = term298.
Proof. exact (MK_COMB (@lem5418125) (@lem5418126)). Qed.
Lemma lem5418129 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5418130 : term298 = term301.
Proof. exact (@lem5418129 term69 term69). Qed.
Lemma lem5418131 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5418132 : term226 = term69.
Proof. exact (EQ_MP (@lem5418131) (@lem940073)). Qed.
Lemma lem5418133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5418134 : term224 = term170.
Proof. exact (MK_COMB (@lem5418133) (@lem5418132)). Qed.
Lemma lem5418135 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5418136 : term301 = term214.
Proof. exact (MK_COMB (@lem5418135) (@lem5418134)). Qed.
Lemma lem5418137 : term298 = term214.
Proof. exact (TRANS (@lem5418130) (@lem5418136)). Qed.
Lemma lem5418138 : term545 = term214.
Proof. exact (TRANS (@lem5418127) (@lem5418137)). Qed.
Lemma lem5418140 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5418141 : term223 = term224.
Proof. exact (@lem5418140 term69 term69). Qed.
Lemma lem5418142 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5418143 : term226 = term69.
Proof. exact (EQ_MP (@lem5418142) (@lem940073)). Qed.
Lemma lem5418144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5418145 : term224 = term170.
Proof. exact (MK_COMB (@lem5418144) (@lem5418143)). Qed.
Lemma lem5418146 : term223 = term170.
Proof. exact (TRANS (@lem5418141) (@lem5418145)). Qed.
Lemma lem5418147 : term216 = term216.
Proof. exact (eq_refl term216). Qed.
Lemma lem5418148 : term546 = term298.
Proof. exact (MK_COMB (@lem5418147) (@lem5418146)). Qed.
Lemma lem5418150 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5418151 : term298 = term301.
Proof. exact (@lem5418150 term69 term69). Qed.
Lemma lem5418152 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5418153 : term226 = term69.
Proof. exact (EQ_MP (@lem5418152) (@lem940073)). Qed.
Lemma lem5418154 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5418155 : term224 = term170.
Proof. exact (MK_COMB (@lem5418154) (@lem5418153)). Qed.
Lemma lem5418156 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5418157 : term301 = term214.
Proof. exact (MK_COMB (@lem5418156) (@lem5418155)). Qed.
Lemma lem5418158 : term298 = term214.
Proof. exact (TRANS (@lem5418151) (@lem5418157)). Qed.
Lemma lem5418159 : term546 = term214.
Proof. exact (TRANS (@lem5418148) (@lem5418158)). Qed.
Lemma lem5418160 : term214 = term546.
Proof. exact (SYM (@lem5418159)). Qed.
Lemma lem5418161 : term545 = term546.
Proof. exact (TRANS (@lem5418138) (@lem5418160)). Qed.
Lemma lem5418162 : term534 = term215.
Proof. exact (@lem5418084 (@lem5418161)). Qed.
Lemma lem5418163 : term533 = term215.
Proof. exact (TRANS (@lem5418050) (@lem5418162)). Qed.
Lemma lem5418165 (x : real) : (term230 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5418166 : term215 = term214.
Proof. exact (@lem5418165 term214). Qed.
Lemma lem5418167 : term533 = term214.
Proof. exact (TRANS (@lem5418163) (@lem5418166)). Qed.
Lemma lem5418168 (_69911 : int) : (term578 _69911) = term561.
Proof. exact (MK_COMB (@lem5418041 _69911) (@lem5418167)). Qed.
Lemma lem5418169 (_69911 : int) : (term577 _69911) = term561.
Proof. exact (TRANS (@lem5417933 _69911) (@lem5418168 _69911)). Qed.
Lemma lem5418170 : term561 = term214.
Proof. exact (@lem1982721 term214). Qed.
Lemma lem5418171 (_69911 : int) : (term577 _69911) = term214.
Proof. exact (TRANS (@lem5418169 _69911) (@lem5418170)). Qed.
Lemma lem5418172 (_69910 : int) (_69911 : int) : (term576 _69910 _69911) = term561.
Proof. exact (MK_COMB (@lem5417932 _69910) (@lem5418171 _69911)). Qed.
Lemma lem5418173 (_69910 : int) (_69911 : int) : (term575 _69910 _69911) = term561.
Proof. exact (TRANS (@lem5417824 _69910 _69911) (@lem5418172 _69910 _69911)). Qed.
Lemma lem5418174 : term561 = term214.
Proof. exact (@lem1982721 term214). Qed.
Lemma lem5418175 (_69910 : int) (_69911 : int) : (term575 _69910 _69911) = term214.
Proof. exact (TRANS (@lem5418173 _69910 _69911) (@lem5418174)). Qed.
Lemma lem5418176 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5418177 (_69910 : int) (_69911 : int) : (term579 _69910 _69911) = term563.
Proof. exact (MK_COMB (@lem5418176) (@lem5418175 _69910 _69911)). Qed.
Lemma lem5418178 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5418179 (_69910 : int) (_69911 : int) : (term574 _69910 _69911) = term564.
Proof. exact (MK_COMB (@lem5418177 _69910 _69911) (@lem5418178)). Qed.
Lemma lem5418180 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : term564.
Proof. exact (EQ_MP (@lem5418179 _69910 _69911) (@lem5417823 _69909 _69910 _69911 h1)). Qed.
Lemma lem5418182 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5418183 : term564 = term565.
Proof. exact (@lem5418182 term153 term214). Qed.
Lemma lem5418185 (x : nat) : (term212 x) = (term213 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5418186 : term214 = term215.
Proof. exact (@lem5418185 term69). Qed.
Lemma lem5418188 (x : nat) : (real_of_num x) = (term210 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5418189 : term153 = term211.
Proof. exact (@lem5418188 (NUMERAL 0)). Qed.
Lemma lem5418190 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5418191 : term155 = term482.
Proof. exact (MK_COMB (@lem5418190) (@lem5418189)). Qed.
Lemma lem5418192 : term565 = term566.
Proof. exact (MK_COMB (@lem5418191) (@lem5418186)). Qed.
Lemma lem5418193 : term567.
Proof. exact (@lem1980026 term153 term170 term214 term170). Qed.
Lemma lem5418195 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5418196 : term245 = term246.
Proof. exact (@lem5418195 (NUMERAL 0) term69). Qed.
Lemma lem5418197 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5418198 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5418199 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5418198 h1) (fun h1 : term246 = True => @lem5418197)). Qed.
Lemma lem5418200 : term246 = True.
Proof. exact (EQ_MP (@lem5418199) (@lem5418197)). Qed.
Lemma lem5418201 : term245 = True.
Proof. exact (TRANS (@lem5418196) (@lem5418200)). Qed.
Lemma lem5418202 : True = term245.
Proof. exact (SYM (@lem5418201)). Qed.
Lemma lem5418203 : term245.
Proof. exact (EQ_MP (@lem5418202) (@lem0)). Qed.
Lemma lem5418204 : term568.
Proof. exact (@lem5418193 (@lem5418203)). Qed.
Lemma lem5418206 (m : nat) (n : nat) : (term244 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5418207 : term245 = term246.
Proof. exact (@lem5418206 (NUMERAL 0) term69). Qed.
Lemma lem5418208 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5418209 (h1 : term247 = (BIT1 0)) : term246 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5418210 : (term247 = (BIT1 0)) = (term246 = True).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5418209 h1) (fun h1 : term246 = True => @lem5418208)). Qed.
Lemma lem5418211 : term246 = True.
Proof. exact (EQ_MP (@lem5418210) (@lem5418208)). Qed.
Lemma lem5418212 : term245 = True.
Proof. exact (TRANS (@lem5418207) (@lem5418211)). Qed.
Lemma lem5418213 : True = term245.
Proof. exact (SYM (@lem5418212)). Qed.
Lemma lem5418214 : term245.
Proof. exact (EQ_MP (@lem5418213) (@lem0)). Qed.
Lemma lem5418215 : term566 = term569.
Proof. exact (@lem5418204 (@lem5418214)). Qed.
Lemma lem5418217 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5418218 : term298 = term301.
Proof. exact (@lem5418217 term69 term69). Qed.
Lemma lem5418219 : (term225 = (BIT1 0)) = (term226 = term69).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5418220 : term226 = term69.
Proof. exact (EQ_MP (@lem5418219) (@lem940073)). Qed.
Lemma lem5418221 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5418222 : term224 = term170.
Proof. exact (MK_COMB (@lem5418221) (@lem5418220)). Qed.
Lemma lem5418223 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5418224 : term301 = term214.
Proof. exact (MK_COMB (@lem5418223) (@lem5418222)). Qed.
Lemma lem5418225 : term298 = term214.
Proof. exact (TRANS (@lem5418218) (@lem5418224)). Qed.
Lemma lem5418227 (x : nat) : (term417 x) = term153.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5418228 : term418 = term153.
Proof. exact (@lem5418227 term69). Qed.
Lemma lem5418229 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5418230 : term489 = term155.
Proof. exact (MK_COMB (@lem5418229) (@lem5418228)). Qed.
Lemma lem5418231 : term569 = term565.
Proof. exact (MK_COMB (@lem5418230) (@lem5418225)). Qed.
Lemma lem5418233 (m : nat) (n : nat) : (term490 m n) = (term491 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5418234 : term565 = term570.
Proof. exact (@lem5418233 (NUMERAL 0) term69). Qed.
Lemma lem5418235 : term247 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5418236 (h1 : term247 = (BIT1 0)) : (term69 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5418237 : (term247 = (BIT1 0)) = ((term69 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term247 = (BIT1 0) => @lem5418236 h1) (fun h1 : (term69 = (NUMERAL 0)) = False => @lem5418235)). Qed.
Lemma lem5418238 : (term69 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5418237) (@lem5418235)). Qed.
Lemma lem5418239 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5418240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5418241 : term494 = (and True).
Proof. exact (MK_COMB (@lem5418240) (@lem5418239)). Qed.
Lemma lem5418242 : term570 = (True /\ False).
Proof. exact (MK_COMB (@lem5418241) (@lem5418238)). Qed.
Lemma lem5418244 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5418245 : term570 = False.
Proof. exact (TRANS (@lem5418242) (@lem5418244)). Qed.
Lemma lem5418246 : term565 = False.
Proof. exact (TRANS (@lem5418234) (@lem5418245)). Qed.
Lemma lem5418247 : term569 = False.
Proof. exact (TRANS (@lem5418231) (@lem5418246)). Qed.
Lemma lem5418248 : term566 = False.
Proof. exact (TRANS (@lem5418215) (@lem5418247)). Qed.
Lemma lem5418249 : term565 = False.
Proof. exact (TRANS (@lem5418192) (@lem5418248)). Qed.
Lemma lem5418250 : term564 = False.
Proof. exact (TRANS (@lem5418183) (@lem5418249)). Qed.
Lemma lem5418251 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term571 _69909 _69910 _69911) : False.
Proof. exact (EQ_MP (@lem5418250) (@lem5418180 _69909 _69910 _69911 h1)). Qed.
Lemma lem5418252 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term399 _69909 _69910 _69911) : False.
Proof. exact (or_elim (@lem5416507 _69909 _69910 _69911 h1) (fun h0 : term516 _69910 _69909 _69911 => @lem5417381 _69910 _69909 _69911 h0) (fun h0 : term571 _69909 _69910 _69911 => @lem5418251 _69909 _69910 _69911 h0)). Qed.
Lemma lem5418253 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term408 _69909 _69910 _69911) : False.
Proof. exact (or_elim (@lem5415012 _69909 _69910 _69911 h1) (fun h0 : term403 _69909 _69910 _69911 => @lem5416506 _69909 _69910 _69911 h0) (fun h0 : term399 _69909 _69910 _69911 => @lem5418252 _69909 _69910 _69911 h0)). Qed.
Lemma lem5418255 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term408 _69909 _69910 _69911) : term408 _69909 _69910 _69911.
Proof. exact (h1). Qed.
Lemma lem5418256 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term408 _69909 _69910 _69911) : (term408 _69909 _69910 _69911) = False.
Proof. exact (prop_ext (fun h2 : term408 _69909 _69910 _69911 => @lem5418253 _69909 _69910 _69911 h1) (fun h2 : False => @lem5418255 _69909 _69910 _69911 h1)). Qed.
Lemma lem5418257 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term408 _69909 _69910 _69911) : False.
Proof. exact (EQ_MP (@lem5418256 _69909 _69910 _69911 h1) (@lem5418255 _69909 _69910 _69911 h1)). Qed.
Lemma lem5418258 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term206 _69909 _69910 _69911) : term206 _69909 _69910 _69911.
Proof. exact (h1). Qed.
Lemma lem5418259 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term206 _69909 _69910 _69911) : term408 _69909 _69910 _69911.
Proof. exact (EQ_MP (@lem5414990 _69909 _69910 _69911) (@lem5418258 _69909 _69910 _69911 h1)). Qed.
Lemma lem5418260 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term206 _69909 _69910 _69911) : (term408 _69909 _69910 _69911) = False.
Proof. exact (prop_ext (fun h2 : term408 _69909 _69910 _69911 => @lem5418257 _69909 _69910 _69911 h2) (fun h2 : False => @lem5418259 _69909 _69910 _69911 h1)). Qed.
Lemma lem5418261 (_69909 : int) (_69910 : int) (_69911 : int) (h1 : term206 _69909 _69910 _69911) : False.
Proof. exact (EQ_MP (@lem5418260 _69909 _69910 _69911 h1) (@lem5418259 _69909 _69910 _69911 h1)). Qed.
Lemma lem5418262 (_69909 : int) (_69910 : int) (_69911 : int) : term580 _69909 _69910 _69911.
Proof. exact (fun h0 : term206 _69909 _69910 _69911 => @lem5418261 _69909 _69910 _69911 h0). Qed.
Lemma lem5418263 (_69909 : int) (_69910 : int) (_69911 : int) : term581 _69909 _69910 _69911.
Proof. exact (@lem1386578 (term582 _69909 _69910 _69911)). Qed.
Lemma lem5418266 (_69909 : int) (_69910 : int) (_69911 : int) : term582 _69909 _69910 _69911.
Proof. exact (@lem5418263 _69909 _69910 _69911 (@lem5418262 _69909 _69910 _69911)). Qed.
Lemma lem5418267 (_69909 : int) (_69911 : int) (_69910 : int) : (term204 _69909 _69910 _69911) = (term146 _69909 _69911 _69910).
Proof. exact (SYM (@lem5413867 _69909 _69910 _69911)). Qed.
Lemma lem5418268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5418269 (_69909 : int) (_69911 : int) (_69910 : int) : (term582 _69909 _69910 _69911) = (term93 _69909 _69911 _69910).
Proof. exact (MK_COMB (@lem5418268) (@lem5418267 _69909 _69911 _69910)). Qed.
Lemma lem5418270 (_69909 : int) (_69911 : int) (_69910 : int) : term93 _69909 _69911 _69910.
Proof. exact (EQ_MP (@lem5418269 _69909 _69911 _69910) (@lem5418266 _69909 _69910 _69911)). Qed.
Lemma lem5418271 (_69909 : int) (_69911 : int) (_69910 : int) : term94 _69909 _69911 _69910.
Proof. exact (EQ_MP (@lem5413478 _69909 _69911 _69910) (@lem5418270 _69909 _69911 _69910)). Qed.
Lemma lem5418272 (m : nat) (x : nat) (n : nat) : term583 m x n.
Proof. exact (@lem5418271 (int_of_num m) (int_of_num x) (int_of_num n)). Qed.
Lemma lem5418273 (m : nat) (x : nat) (n : nat) : term584 m x n.
Proof. exact (@lem5418272 m x n (@lem5413471 m)). Qed.
Lemma lem5418274 (m : nat) (x : nat) (n : nat) : term585 m x n.
Proof. exact (@lem5418273 m x n (@lem5413474 n)). Qed.
Lemma lem5418275 (m : nat) (x : nat) (n : nat) : term88 m x n.
Proof. exact (@lem5418274 m x n (@lem5413477 x)). Qed.
Lemma lem5418276 (m : nat) (n : nat) : term90 m n.
Proof. exact (fun x : nat => @lem5418275 m x n). Qed.
Lemma lem5418277 (m : nat) (n : nat) : (term90 m n) = (term5 m n).
Proof. exact (SYM (@lem5413468 m n)). Qed.
Lemma lem5418278 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem5418277 m n) (@lem5418276 m n)). Qed.
Lemma lem5418279 (m : nat) (n : nat) : (term5 m n) = ((term5 m n) = True).
Proof. exact (@lem7 (term5 m n)). Qed.
Lemma lem5418280 (m : nat) (n : nat) : (term5 m n) = True.
Proof. exact (EQ_MP (@lem5418279 m n) (@lem5418278 m n)). Qed.
Lemma lem5418281 (m : nat) (n : nat) : True = (term5 m n).
Proof. exact (SYM (@lem5418280 m n)). Qed.
Lemma lem5418282 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem5418281 m n) (@lem0)). Qed.
Lemma lem5418283 (m : nat) (n : nat) (h1 : term29 m n) : term3 m n.
Proof. exact (@lem5418282 m n (@lem5400877 m n h1)). Qed.
