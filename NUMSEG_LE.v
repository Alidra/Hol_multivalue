Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_LE_term_abbrevs.
Require Import EXTENSION_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import thm0_spec.
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
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm19158_spec.
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
Require Import thm1982757_spec.
Require Import thm1982759_spec.
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
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5476958 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5476959 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem5476958 _83095 p). Qed.
Lemma lem5476960 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem5476961 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem5476960 _83095 p) (@lem5476959 _83095 p)). Qed.
Lemma lem5476962 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem5476961 _83095 p x). Qed.
Lemma lem5476963 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem5476972 (m : nat) : term5 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5476973 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem5476974 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem5476973 m) (@lem5476972 m)). Qed.
Lemma lem5476975 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem5476974 m n). Qed.
Lemma lem5476976 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem5476977 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem5476976 m n) (@lem5476975 m n)). Qed.
Lemma lem5476978 (m : nat) (n : nat) (p : nat) : term9 m n p.
Proof. exact (@lem5476977 m n p). Qed.
Lemma lem5476979 (m : nat) (p : nat) (n : nat) : (term9 m n p) = ((term10 p m n) = (term11 m p n)).
Proof. exact (eq_refl (term9 m n p)). Qed.
Lemma lem5476981 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5476982 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem5476983 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem5476982 A s) (@lem5476981 A s)). Qed.
Lemma lem5476984 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem5476983 A s t). Qed.
Lemma lem5476985 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = ((s = t) = (term15 A s t)).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem5476994 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem5476985 A s t) (@lem5476984 A s t)). Qed.
Lemma lem5476995 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term16 s t).
Proof. exact (@lem5476994 nat s t). Qed.
Lemma lem5476996 (n : nat) : ((term17 n) = (term18 n)) = (term19 n).
Proof. exact (@lem5476995 (term17 n) (term18 n)). Qed.
Lemma lem5477006 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5476963 _83095 p x) (@lem5476962 _83095 p x)). Qed.
Lemma lem5477007 (p : nat -> Prop) (x : nat) : (term20 x p) = (p x).
Proof. exact (@lem5477006 nat p x). Qed.
Lemma lem5477008 (n : nat) (x : nat) : (term21 x n) = (term22 n x).
Proof. exact (@lem5477007 (term23 n) x). Qed.
Lemma lem5477009 (x : nat) (n : nat) : (term22 n x) = (Peano.le x n).
Proof. exact (eq_refl (term22 n x)). Qed.
Lemma lem5477010 (GEN_PVAR_231 : nat) : (@SETSPEC nat GEN_PVAR_231) = (@SETSPEC nat GEN_PVAR_231).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_231)). Qed.
Lemma lem5477011 (GEN_PVAR_231 : nat) (x : nat) (n : nat) : (term24 GEN_PVAR_231 n x) = (term25 GEN_PVAR_231 x n).
Proof. exact (MK_COMB (@lem5477010 GEN_PVAR_231) (@lem5477009 x n)). Qed.
Lemma lem5477012 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5477013 (GEN_PVAR_231 : nat) (n : nat) (x : nat) : (term26 GEN_PVAR_231 n x) = (term27 GEN_PVAR_231 n x).
Proof. exact (MK_COMB (@lem5477011 GEN_PVAR_231 x n) (@lem5477012 x)). Qed.
Lemma lem5477014 (GEN_PVAR_231 : nat) (n : nat) : (term28 GEN_PVAR_231 n) = (term29 GEN_PVAR_231 n).
Proof. exact (fun_ext (fun x : nat => @lem5477013 GEN_PVAR_231 n x)). Qed.
Lemma lem5477015 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5477016 (GEN_PVAR_231 : nat) (n : nat) : (term30 GEN_PVAR_231 n) = (term31 GEN_PVAR_231 n).
Proof. exact (MK_COMB (@lem5477015) (@lem5477014 GEN_PVAR_231 n)). Qed.
Lemma lem5477017 (n : nat) : (term32 n) = (term33 n).
Proof. exact (fun_ext (fun GEN_PVAR_231 : nat => @lem5477016 GEN_PVAR_231 n)). Qed.
Lemma lem5477018 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5477019 (n : nat) : (term34 n) = (term17 n).
Proof. exact (MK_COMB (@lem5477018) (@lem5477017 n)). Qed.
Lemma lem5477020 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5477021 (x : nat) (n : nat) : (term21 x n) = (term35 x n).
Proof. exact (MK_COMB (@lem5477020 x) (@lem5477019 n)). Qed.
Lemma lem5477022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5477023 (x : nat) (n : nat) : (term36 x n) = (term37 x n).
Proof. exact (MK_COMB (@lem5477022) (@lem5477021 x n)). Qed.
Lemma lem5477024 (x : nat) (n : nat) : (term22 n x) = (Peano.le x n).
Proof. exact (eq_refl (term22 n x)). Qed.
Lemma lem5477025 (x : nat) (n : nat) : ((term21 x n) = (term22 n x)) = ((term35 x n) = (Peano.le x n)).
Proof. exact (MK_COMB (@lem5477023 x n) (@lem5477024 x n)). Qed.
Lemma lem5477026 (x : nat) (n : nat) : (term35 x n) = (Peano.le x n).
Proof. exact (EQ_MP (@lem5477025 x n) (@lem5477008 n x)). Qed.
Lemma lem5477027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5477028 (x : nat) (n : nat) : (term37 x n) = (term38 x n).
Proof. exact (MK_COMB (@lem5477027) (@lem5477026 x n)). Qed.
Lemma lem5477030 (m : nat) (p : nat) (n : nat) : (term10 p m n) = (term11 m p n).
Proof. exact (EQ_MP (@lem5476979 m p n) (@lem5476978 m n p)). Qed.
Lemma lem5477031 (x : nat) (n : nat) : (term39 x n) = (term40 x n).
Proof. exact (@lem5477030 (NUMERAL 0) x n). Qed.
Lemma lem5477034 (x : nat) (n : nat) : ((term35 x n) = (term39 x n)) = ((Peano.le x n) = (term40 x n)).
Proof. exact (MK_COMB (@lem5477028 x n) (@lem5477031 x n)). Qed.
Lemma lem5477039 (n : nat) : (term41 n) = (term42 n).
Proof. exact (fun_ext (fun x : nat => @lem5477034 x n)). Qed.
Lemma lem5477040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477041 (n : nat) : (term19 n) = (term43 n).
Proof. exact (MK_COMB (@lem5477040) (@lem5477039 n)). Qed.
Lemma lem5477046 (n : nat) : ((term17 n) = (term18 n)) = (term43 n).
Proof. exact (TRANS (@lem5476996 n) (@lem5477041 n)). Qed.
Lemma lem5477047 : term44 = term45.
Proof. exact (fun_ext (fun n : nat => @lem5477046 n)). Qed.
Lemma lem5477048 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477049 : term46 = term47.
Proof. exact (MK_COMB (@lem5477048) (@lem5477047)). Qed.
Lemma lem5477054 : term47 = term46.
Proof. exact (SYM (@lem5477049)). Qed.
Lemma lem5477076 (x : nat) (n : nat) : ((Peano.le x n) = (term40 x n)) = ((Peano.le x n) = (term40 x n)).
Proof. exact (eq_refl ((Peano.le x n) = (term40 x n))). Qed.
Lemma lem5477077 (n : nat) : (term42 n) = (term42 n).
Proof. exact (fun_ext (fun x : nat => @lem5477076 x n)). Qed.
Lemma lem5477078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477079 (n : nat) : (term43 n) = (term43 n).
Proof. exact (MK_COMB (@lem5477078) (@lem5477077 n)). Qed.
Lemma lem5477080 : term45 = term45.
Proof. exact (fun_ext (fun n : nat => @lem5477079 n)). Qed.
Lemma lem5477081 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477083 : term47 = term47.
Proof. exact (MK_COMB (@lem5477081) (@lem5477080)). Qed.
Lemma lem5477094 (x : nat) (n : nat) : (term48 x n) = (term49 x n).
Proof. exact (@lem17045 (term50 x) (Peano.le x n)). Qed.
Lemma lem5477100 (x : nat) (n : nat) : (term51 x n) = (term51 x n).
Proof. exact (eq_refl (term51 x n)). Qed.
Lemma lem5477102 (x : nat) (n : nat) : (term52 x n) = (term52 x n).
Proof. exact (eq_refl (term52 x n)). Qed.
Lemma lem5477103 (x : nat) (n : nat) : (term53 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem5477102 x n) (@lem5477094 x n)). Qed.
Lemma lem5477104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477105 (x : nat) (n : nat) : (term55 x n) = (term56 x n).
Proof. exact (MK_COMB (@lem5477104) (@lem5477103 x n)). Qed.
Lemma lem5477106 (x : nat) (n : nat) : (term57 x n) = (term58 x n).
Proof. exact (MK_COMB (@lem5477105 x n) (@lem5477100 x n)). Qed.
Lemma lem5477107 (x : nat) (n : nat) : ((Peano.le x n) = (term40 x n)) = (term57 x n).
Proof. exact (@lem17784 (Peano.le x n) (term40 x n)). Qed.
Lemma lem5477108 (x : nat) (n : nat) : ((Peano.le x n) = (term40 x n)) = (term58 x n).
Proof. exact (TRANS (@lem5477107 x n) (@lem5477106 x n)). Qed.
Lemma lem5477109 (n : nat) : (term42 n) = (term59 n).
Proof. exact (fun_ext (fun x : nat => @lem5477108 x n)). Qed.
Lemma lem5477110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477111 (n : nat) : (term43 n) = (term60 n).
Proof. exact (MK_COMB (@lem5477110) (@lem5477109 n)). Qed.
Lemma lem5477112 : term45 = term61.
Proof. exact (fun_ext (fun n : nat => @lem5477111 n)). Qed.
Lemma lem5477113 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477114 : term47 = term62.
Proof. exact (MK_COMB (@lem5477113) (@lem5477112)). Qed.
Lemma lem5477115 : term47 = term62.
Proof. exact (TRANS (@lem5477083) (@lem5477114)). Qed.
Lemma lem5477116 (x : nat) (n : nat) : (term58 x n) = (term58 x n).
Proof. exact (eq_refl (term58 x n)). Qed.
Lemma lem5477117 (n : nat) : (term59 n) = (term59 n).
Proof. exact (fun_ext (fun x : nat => @lem5477116 x n)). Qed.
Lemma lem5477118 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477119 (n : nat) : (term60 n) = (term60 n).
Proof. exact (MK_COMB (@lem5477118) (@lem5477117 n)). Qed.
Lemma lem5477120 : term61 = term61.
Proof. exact (fun_ext (fun n : nat => @lem5477119 n)). Qed.
Lemma lem5477121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477122 : term62 = term62.
Proof. exact (MK_COMB (@lem5477121) (@lem5477120)). Qed.
Lemma lem5477147 : term47 = term62.
Proof. exact (TRANS (@lem5477115) (@lem5477122)). Qed.
Lemma lem5477198 (x : nat) (n : nat) : (term58 x n) = (term58 x n).
Proof. exact (eq_refl (term58 x n)). Qed.
Lemma lem5477199 (n : nat) : (term59 n) = (term59 n).
Proof. exact (fun_ext (fun x : nat => @lem5477198 x n)). Qed.
Lemma lem5477200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477201 (n : nat) : (term60 n) = (term60 n).
Proof. exact (MK_COMB (@lem5477200) (@lem5477199 n)). Qed.
Lemma lem5477202 : term61 = term61.
Proof. exact (fun_ext (fun n : nat => @lem5477201 n)). Qed.
Lemma lem5477203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477204 : term62 = term62.
Proof. exact (MK_COMB (@lem5477203) (@lem5477202)). Qed.
Lemma lem5477207 : term47 = term62.
Proof. exact (TRANS (@lem5477147) (@lem5477204)). Qed.
Lemma lem5477209 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5477210 (x : nat) (n : nat) : (Peano.le x n) = (term63 x n).
Proof. exact (@lem5477209 x n). Qed.
Lemma lem5477211 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5477212 (x : nat) (n : nat) : (term52 x n) = (term64 x n).
Proof. exact (MK_COMB (@lem5477211) (@lem5477210 x n)). Qed.
Lemma lem5477214 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5477215 (x : nat) : (term50 x) = (term65 x).
Proof. exact (@lem5477214 (NUMERAL 0) x). Qed.
Lemma lem5477216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5477217 (x : nat) : (term66 x) = (term67 x).
Proof. exact (MK_COMB (@lem5477216) (@lem5477215 x)). Qed.
Lemma lem5477218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5477219 (x : nat) : (term68 x) = (term69 x).
Proof. exact (MK_COMB (@lem5477218) (@lem5477217 x)). Qed.
Lemma lem5477221 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5477222 (x : nat) (n : nat) : (Peano.le x n) = (term63 x n).
Proof. exact (@lem5477221 x n). Qed.
Lemma lem5477223 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5477224 (x : nat) (n : nat) : (term70 x n) = (term71 x n).
Proof. exact (MK_COMB (@lem5477223) (@lem5477222 x n)). Qed.
Lemma lem5477225 (x : nat) (n : nat) : (term49 x n) = (term72 x n).
Proof. exact (MK_COMB (@lem5477219 x) (@lem5477224 x n)). Qed.
Lemma lem5477226 (x : nat) (n : nat) : (term54 x n) = (term73 x n).
Proof. exact (MK_COMB (@lem5477212 x n) (@lem5477225 x n)). Qed.
Lemma lem5477227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477228 (x : nat) (n : nat) : (term56 x n) = (term74 x n).
Proof. exact (MK_COMB (@lem5477227) (@lem5477226 x n)). Qed.
Lemma lem5477230 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5477231 (x : nat) (n : nat) : (Peano.le x n) = (term63 x n).
Proof. exact (@lem5477230 x n). Qed.
Lemma lem5477232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5477233 (x : nat) (n : nat) : (term70 x n) = (term71 x n).
Proof. exact (MK_COMB (@lem5477232) (@lem5477231 x n)). Qed.
Lemma lem5477234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5477235 (x : nat) (n : nat) : (term75 x n) = (term76 x n).
Proof. exact (MK_COMB (@lem5477234) (@lem5477233 x n)). Qed.
Lemma lem5477237 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5477238 (x : nat) : (term50 x) = (term65 x).
Proof. exact (@lem5477237 (NUMERAL 0) x). Qed.
Lemma lem5477239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477240 (x : nat) : (term77 x) = (term78 x).
Proof. exact (MK_COMB (@lem5477239) (@lem5477238 x)). Qed.
Lemma lem5477242 (m : nat) (n : nat) : (Peano.le m n) = (term63 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5477243 (x : nat) (n : nat) : (Peano.le x n) = (term63 x n).
Proof. exact (@lem5477242 x n). Qed.
Lemma lem5477244 (x : nat) (n : nat) : (term40 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem5477240 x) (@lem5477243 x n)). Qed.
Lemma lem5477245 (x : nat) (n : nat) : (term51 x n) = (term80 x n).
Proof. exact (MK_COMB (@lem5477235 x n) (@lem5477244 x n)). Qed.
Lemma lem5477246 (x : nat) (n : nat) : (term58 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem5477228 x n) (@lem5477245 x n)). Qed.
Lemma lem5477247 (n : nat) : (term59 n) = (term82 n).
Proof. exact (fun_ext (fun x : nat => @lem5477246 x n)). Qed.
Lemma lem5477248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477249 (n : nat) : (term60 n) = (term83 n).
Proof. exact (MK_COMB (@lem5477248) (@lem5477247 n)). Qed.
Lemma lem5477250 : term61 = term84.
Proof. exact (fun_ext (fun n : nat => @lem5477249 n)). Qed.
Lemma lem5477251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5477252 : term62 = term85.
Proof. exact (MK_COMB (@lem5477251) (@lem5477250)). Qed.
Lemma lem5477253 : term47 = term85.
Proof. exact (TRANS (@lem5477207) (@lem5477252)). Qed.
Lemma lem5477254 (n : nat) : term86 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5477255 (n : nat) : (term86 n) = (term65 n).
Proof. exact (eq_refl (term86 n)). Qed.
Lemma lem5477256 (n : nat) : term65 n.
Proof. exact (EQ_MP (@lem5477255 n) (@lem5477254 n)). Qed.
Lemma lem5477257 (x : nat) : term86 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5477258 (x : nat) : (term86 x) = (term65 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem5477259 (x : nat) : term65 x.
Proof. exact (EQ_MP (@lem5477258 x) (@lem5477257 x)). Qed.
Lemma lem5477260 (_70591 : int) (_70590 : int) : (term87 _70591 _70590) = (term88 _70591 _70590).
Proof. exact (@lem2318604 (term88 _70591 _70590)). Qed.
Lemma lem5477285 (_70591 : int) : (term89 _70591) = (term90 _70591).
Proof. exact (@lem16933 (term90 _70591)). Qed.
Lemma lem5477288 (_70591 : int) (_70590 : int) : (term91 _70591 _70590) = (int_le _70591 _70590).
Proof. exact (@lem16933 (int_le _70591 _70590)). Qed.
Lemma lem5477289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477290 (_70591 : int) : (term92 _70591) = (term93 _70591).
Proof. exact (MK_COMB (@lem5477289) (@lem5477285 _70591)). Qed.
Lemma lem5477291 (_70591 : int) (_70590 : int) : (term94 _70591 _70590) = (term95 _70591 _70590).
Proof. exact (MK_COMB (@lem5477290 _70591) (@lem5477288 _70591 _70590)). Qed.
Lemma lem5477292 (_70591 : int) (_70590 : int) : (term96 _70591 _70590) = (term94 _70591 _70590).
Proof. exact (@lem17160 (term97 _70591) (term98 _70591 _70590)). Qed.
Lemma lem5477293 (_70591 : int) (_70590 : int) : (term96 _70591 _70590) = (term95 _70591 _70590).
Proof. exact (TRANS (@lem5477292 _70591 _70590) (@lem5477291 _70591 _70590)). Qed.
Lemma lem5477295 (_70591 : int) (_70590 : int) : (term99 _70591 _70590) = (term99 _70591 _70590).
Proof. exact (eq_refl (term99 _70591 _70590)). Qed.
Lemma lem5477296 (_70591 : int) (_70590 : int) : (term100 _70591 _70590) = (term101 _70591 _70590).
Proof. exact (MK_COMB (@lem5477295 _70591 _70590) (@lem5477293 _70591 _70590)). Qed.
Lemma lem5477297 (_70591 : int) (_70590 : int) : (term102 _70591 _70590) = (term100 _70591 _70590).
Proof. exact (@lem17160 (int_le _70591 _70590) (term103 _70591 _70590)). Qed.
Lemma lem5477298 (_70591 : int) (_70590 : int) : (term102 _70591 _70590) = (term101 _70591 _70590).
Proof. exact (TRANS (@lem5477297 _70591 _70590) (@lem5477296 _70591 _70590)). Qed.
Lemma lem5477301 (_70591 : int) (_70590 : int) : (term91 _70591 _70590) = (int_le _70591 _70590).
Proof. exact (@lem16933 (int_le _70591 _70590)). Qed.
Lemma lem5477308 (_70591 : int) (_70590 : int) : (term104 _70591 _70590) = (term103 _70591 _70590).
Proof. exact (@lem17045 (term90 _70591) (int_le _70591 _70590)). Qed.
Lemma lem5477309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477310 (_70591 : int) (_70590 : int) : (term105 _70591 _70590) = (term106 _70591 _70590).
Proof. exact (MK_COMB (@lem5477309) (@lem5477301 _70591 _70590)). Qed.
Lemma lem5477311 (_70591 : int) (_70590 : int) : (term107 _70591 _70590) = (term108 _70591 _70590).
Proof. exact (MK_COMB (@lem5477310 _70591 _70590) (@lem5477308 _70591 _70590)). Qed.
Lemma lem5477312 (_70591 : int) (_70590 : int) : (term109 _70591 _70590) = (term107 _70591 _70590).
Proof. exact (@lem17160 (term98 _70591 _70590) (term95 _70591 _70590)). Qed.
Lemma lem5477313 (_70591 : int) (_70590 : int) : (term109 _70591 _70590) = (term108 _70591 _70590).
Proof. exact (TRANS (@lem5477312 _70591 _70590) (@lem5477311 _70591 _70590)). Qed.
Lemma lem5477314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5477315 (_70591 : int) (_70590 : int) : (term110 _70591 _70590) = (term111 _70591 _70590).
Proof. exact (MK_COMB (@lem5477314) (@lem5477298 _70591 _70590)). Qed.
Lemma lem5477316 (_70591 : int) (_70590 : int) : (term112 _70591 _70590) = (term113 _70591 _70590).
Proof. exact (MK_COMB (@lem5477315 _70591 _70590) (@lem5477313 _70591 _70590)). Qed.
Lemma lem5477317 (_70591 : int) (_70590 : int) : (term114 _70591 _70590) = (term112 _70591 _70590).
Proof. exact (@lem17045 (term115 _70591 _70590) (term116 _70591 _70590)). Qed.
Lemma lem5477318 (_70591 : int) (_70590 : int) : (term114 _70591 _70590) = (term113 _70591 _70590).
Proof. exact (TRANS (@lem5477317 _70591 _70590) (@lem5477316 _70591 _70590)). Qed.
Lemma lem5477320 (_70591 : int) : (term93 _70591) = (term93 _70591).
Proof. exact (eq_refl (term93 _70591)). Qed.
Lemma lem5477321 (_70591 : int) (_70590 : int) : (term117 _70591 _70590) = (term118 _70591 _70590).
Proof. exact (MK_COMB (@lem5477320 _70591) (@lem5477318 _70591 _70590)). Qed.
Lemma lem5477322 (_70591 : int) (_70590 : int) : (term119 _70591 _70590) = (term117 _70591 _70590).
Proof. exact (@lem17362 (term90 _70591) (term120 _70591 _70590)). Qed.
Lemma lem5477323 (_70591 : int) (_70590 : int) : (term119 _70591 _70590) = (term118 _70591 _70590).
Proof. exact (TRANS (@lem5477322 _70591 _70590) (@lem5477321 _70591 _70590)). Qed.
Lemma lem5477325 (_70590 : int) : (term93 _70590) = (term93 _70590).
Proof. exact (eq_refl (term93 _70590)). Qed.
Lemma lem5477326 (_70591 : int) (_70590 : int) : (term121 _70591 _70590) = (term122 _70591 _70590).
Proof. exact (MK_COMB (@lem5477325 _70590) (@lem5477323 _70591 _70590)). Qed.
Lemma lem5477327 (_70591 : int) (_70590 : int) : (term123 _70591 _70590) = (term121 _70591 _70590).
Proof. exact (@lem17362 (term90 _70590) (term124 _70591 _70590)). Qed.
Lemma lem5477365 (_70591 : int) (_70590 : int) : (term123 _70591 _70590) = (term122 _70591 _70590).
Proof. exact (TRANS (@lem5477327 _70591 _70590) (@lem5477326 _70591 _70590)). Qed.
Lemma lem5477368 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5477369 (_70590 : int) : (term90 _70590) = (term126 _70590).
Proof. exact (@lem5477368 term127 _70590). Qed.
Lemma lem5477371 (n : nat) : (term128 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5477372 : term129 = term130.
Proof. exact (@lem5477371 (NUMERAL 0)). Qed.
Lemma lem5477373 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5477374 : term131 = term132.
Proof. exact (MK_COMB (@lem5477373) (@lem5477372)). Qed.
Lemma lem5477375 (_70590 : int) : (real_of_int _70590) = (real_of_int _70590).
Proof. exact (eq_refl (real_of_int _70590)). Qed.
Lemma lem5477376 (_70590 : int) : (term126 _70590) = (term133 _70590).
Proof. exact (MK_COMB (@lem5477374) (@lem5477375 _70590)). Qed.
Lemma lem5477378 (_70590 : int) : (term90 _70590) = (term133 _70590).
Proof. exact (TRANS (@lem5477369 _70590) (@lem5477376 _70590)). Qed.
Lemma lem5477381 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5477382 (_70591 : int) : (term90 _70591) = (term126 _70591).
Proof. exact (@lem5477381 term127 _70591). Qed.
Lemma lem5477384 (n : nat) : (term128 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5477385 : term129 = term130.
Proof. exact (@lem5477384 (NUMERAL 0)). Qed.
Lemma lem5477386 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5477387 : term131 = term132.
Proof. exact (MK_COMB (@lem5477386) (@lem5477385)). Qed.
Lemma lem5477388 (_70591 : int) : (real_of_int _70591) = (real_of_int _70591).
Proof. exact (eq_refl (real_of_int _70591)). Qed.
Lemma lem5477389 (_70591 : int) : (term126 _70591) = (term133 _70591).
Proof. exact (MK_COMB (@lem5477387) (@lem5477388 _70591)). Qed.
Lemma lem5477391 (_70591 : int) : (term90 _70591) = (term133 _70591).
Proof. exact (TRANS (@lem5477382 _70591) (@lem5477389 _70591)). Qed.
Lemma lem5477393 (y : int) (x : int) : (term98 x y) = (term134 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5477394 (_70590 : int) (_70591 : int) : (term98 _70591 _70590) = (term134 _70590 _70591).
Proof. exact (@lem5477393 _70590 _70591). Qed.
Lemma lem5477396 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5477397 (_70590 : int) (_70591 : int) : (term134 _70590 _70591) = (term135 _70590 _70591).
Proof. exact (@lem5477396 (term136 _70590) _70591). Qed.
Lemma lem5477399 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5477400 (_70590 : int) : (term139 _70590) = (term140 _70590).
Proof. exact (@lem5477399 _70590 term141). Qed.
Lemma lem5477402 (n : nat) : (term128 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5477403 : term142 = term143.
Proof. exact (@lem5477402 term144). Qed.
Lemma lem5477404 (_70590 : int) : (term145 _70590) = (term145 _70590).
Proof. exact (eq_refl (term145 _70590)). Qed.
Lemma lem5477405 (_70590 : int) : (term140 _70590) = (term146 _70590).
Proof. exact (MK_COMB (@lem5477404 _70590) (@lem5477403)). Qed.
Lemma lem5477406 (_70590 : int) : (term139 _70590) = (term146 _70590).
Proof. exact (TRANS (@lem5477400 _70590) (@lem5477405 _70590)). Qed.
Lemma lem5477407 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5477408 (_70590 : int) : (term147 _70590) = (term148 _70590).
Proof. exact (MK_COMB (@lem5477407) (@lem5477406 _70590)). Qed.
Lemma lem5477409 (_70591 : int) : (real_of_int _70591) = (real_of_int _70591).
Proof. exact (eq_refl (real_of_int _70591)). Qed.
Lemma lem5477410 (_70590 : int) (_70591 : int) : (term135 _70590 _70591) = (term149 _70590 _70591).
Proof. exact (MK_COMB (@lem5477408 _70590) (@lem5477409 _70591)). Qed.
Lemma lem5477411 (_70590 : int) (_70591 : int) : (term134 _70590 _70591) = (term149 _70590 _70591).
Proof. exact (TRANS (@lem5477397 _70590 _70591) (@lem5477410 _70590 _70591)). Qed.
Lemma lem5477412 (_70590 : int) (_70591 : int) : (term98 _70591 _70590) = (term149 _70590 _70591).
Proof. exact (TRANS (@lem5477394 _70590 _70591) (@lem5477411 _70590 _70591)). Qed.
Lemma lem5477415 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5477416 (_70591 : int) : (term90 _70591) = (term126 _70591).
Proof. exact (@lem5477415 term127 _70591). Qed.
Lemma lem5477418 (n : nat) : (term128 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5477419 : term129 = term130.
Proof. exact (@lem5477418 (NUMERAL 0)). Qed.
Lemma lem5477420 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5477421 : term131 = term132.
Proof. exact (MK_COMB (@lem5477420) (@lem5477419)). Qed.
Lemma lem5477422 (_70591 : int) : (real_of_int _70591) = (real_of_int _70591).
Proof. exact (eq_refl (real_of_int _70591)). Qed.
Lemma lem5477423 (_70591 : int) : (term126 _70591) = (term133 _70591).
Proof. exact (MK_COMB (@lem5477421) (@lem5477422 _70591)). Qed.
Lemma lem5477425 (_70591 : int) : (term90 _70591) = (term133 _70591).
Proof. exact (TRANS (@lem5477416 _70591) (@lem5477423 _70591)). Qed.
Lemma lem5477428 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5477430 (_70591 : int) (_70590 : int) : (int_le _70591 _70590) = (term125 _70591 _70590).
Proof. exact (@lem5477428 _70591 _70590). Qed.
Lemma lem5477431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477432 (_70591 : int) : (term93 _70591) = (term150 _70591).
Proof. exact (MK_COMB (@lem5477431) (@lem5477425 _70591)). Qed.
Lemma lem5477433 (_70591 : int) (_70590 : int) : (term95 _70591 _70590) = (term151 _70591 _70590).
Proof. exact (MK_COMB (@lem5477432 _70591) (@lem5477430 _70591 _70590)). Qed.
Lemma lem5477434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477435 (_70590 : int) (_70591 : int) : (term99 _70591 _70590) = (term152 _70590 _70591).
Proof. exact (MK_COMB (@lem5477434) (@lem5477412 _70590 _70591)). Qed.
Lemma lem5477436 (_70591 : int) (_70590 : int) : (term101 _70591 _70590) = (term153 _70591 _70590).
Proof. exact (MK_COMB (@lem5477435 _70590 _70591) (@lem5477433 _70591 _70590)). Qed.
Lemma lem5477439 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5477441 (_70591 : int) (_70590 : int) : (int_le _70591 _70590) = (term125 _70591 _70590).
Proof. exact (@lem5477439 _70591 _70590). Qed.
Lemma lem5477443 (y : int) (x : int) : (term98 x y) = (term134 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5477444 (_70591 : int) : (term97 _70591) = (term154 _70591).
Proof. exact (@lem5477443 _70591 term127). Qed.
Lemma lem5477446 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5477447 (_70591 : int) : (term154 _70591) = (term155 _70591).
Proof. exact (@lem5477446 (term136 _70591) term127). Qed.
Lemma lem5477449 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5477450 (_70591 : int) : (term139 _70591) = (term140 _70591).
Proof. exact (@lem5477449 _70591 term141). Qed.
Lemma lem5477452 (n : nat) : (term128 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5477453 : term142 = term143.
Proof. exact (@lem5477452 term144). Qed.
Lemma lem5477454 (_70591 : int) : (term145 _70591) = (term145 _70591).
Proof. exact (eq_refl (term145 _70591)). Qed.
Lemma lem5477455 (_70591 : int) : (term140 _70591) = (term146 _70591).
Proof. exact (MK_COMB (@lem5477454 _70591) (@lem5477453)). Qed.
Lemma lem5477456 (_70591 : int) : (term139 _70591) = (term146 _70591).
Proof. exact (TRANS (@lem5477450 _70591) (@lem5477455 _70591)). Qed.
Lemma lem5477457 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5477458 (_70591 : int) : (term147 _70591) = (term148 _70591).
Proof. exact (MK_COMB (@lem5477457) (@lem5477456 _70591)). Qed.
Lemma lem5477460 (n : nat) : (term128 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5477461 : term129 = term130.
Proof. exact (@lem5477460 (NUMERAL 0)). Qed.
Lemma lem5477462 (_70591 : int) : (term155 _70591) = (term156 _70591).
Proof. exact (MK_COMB (@lem5477458 _70591) (@lem5477461)). Qed.
Lemma lem5477463 (_70591 : int) : (term154 _70591) = (term156 _70591).
Proof. exact (TRANS (@lem5477447 _70591) (@lem5477462 _70591)). Qed.
Lemma lem5477464 (_70591 : int) : (term97 _70591) = (term156 _70591).
Proof. exact (TRANS (@lem5477444 _70591) (@lem5477463 _70591)). Qed.
Lemma lem5477466 (y : int) (x : int) : (term98 x y) = (term134 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5477467 (_70590 : int) (_70591 : int) : (term98 _70591 _70590) = (term134 _70590 _70591).
Proof. exact (@lem5477466 _70590 _70591). Qed.
Lemma lem5477469 (x : int) (y : int) : (int_le x y) = (term125 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5477470 (_70590 : int) (_70591 : int) : (term134 _70590 _70591) = (term135 _70590 _70591).
Proof. exact (@lem5477469 (term136 _70590) _70591). Qed.
Lemma lem5477472 (x : int) (y : int) : (term137 x y) = (term138 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5477473 (_70590 : int) : (term139 _70590) = (term140 _70590).
Proof. exact (@lem5477472 _70590 term141). Qed.
Lemma lem5477475 (n : nat) : (term128 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5477476 : term142 = term143.
Proof. exact (@lem5477475 term144). Qed.
Lemma lem5477477 (_70590 : int) : (term145 _70590) = (term145 _70590).
Proof. exact (eq_refl (term145 _70590)). Qed.
Lemma lem5477478 (_70590 : int) : (term140 _70590) = (term146 _70590).
Proof. exact (MK_COMB (@lem5477477 _70590) (@lem5477476)). Qed.
Lemma lem5477479 (_70590 : int) : (term139 _70590) = (term146 _70590).
Proof. exact (TRANS (@lem5477473 _70590) (@lem5477478 _70590)). Qed.
Lemma lem5477480 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5477481 (_70590 : int) : (term147 _70590) = (term148 _70590).
Proof. exact (MK_COMB (@lem5477480) (@lem5477479 _70590)). Qed.
Lemma lem5477482 (_70591 : int) : (real_of_int _70591) = (real_of_int _70591).
Proof. exact (eq_refl (real_of_int _70591)). Qed.
Lemma lem5477483 (_70590 : int) (_70591 : int) : (term135 _70590 _70591) = (term149 _70590 _70591).
Proof. exact (MK_COMB (@lem5477481 _70590) (@lem5477482 _70591)). Qed.
Lemma lem5477484 (_70590 : int) (_70591 : int) : (term134 _70590 _70591) = (term149 _70590 _70591).
Proof. exact (TRANS (@lem5477470 _70590 _70591) (@lem5477483 _70590 _70591)). Qed.
Lemma lem5477485 (_70590 : int) (_70591 : int) : (term98 _70591 _70590) = (term149 _70590 _70591).
Proof. exact (TRANS (@lem5477467 _70590 _70591) (@lem5477484 _70590 _70591)). Qed.
Lemma lem5477486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5477487 (_70591 : int) : (term157 _70591) = (term158 _70591).
Proof. exact (MK_COMB (@lem5477486) (@lem5477464 _70591)). Qed.
Lemma lem5477488 (_70590 : int) (_70591 : int) : (term103 _70591 _70590) = (term159 _70590 _70591).
Proof. exact (MK_COMB (@lem5477487 _70591) (@lem5477485 _70590 _70591)). Qed.
Lemma lem5477489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477490 (_70591 : int) (_70590 : int) : (term106 _70591 _70590) = (term160 _70591 _70590).
Proof. exact (MK_COMB (@lem5477489) (@lem5477441 _70591 _70590)). Qed.
Lemma lem5477491 (_70590 : int) (_70591 : int) : (term108 _70591 _70590) = (term161 _70590 _70591).
Proof. exact (MK_COMB (@lem5477490 _70591 _70590) (@lem5477488 _70590 _70591)). Qed.
Lemma lem5477492 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5477493 (_70591 : int) (_70590 : int) : (term111 _70591 _70590) = (term162 _70591 _70590).
Proof. exact (MK_COMB (@lem5477492) (@lem5477436 _70591 _70590)). Qed.
Lemma lem5477494 (_70590 : int) (_70591 : int) : (term113 _70591 _70590) = (term163 _70590 _70591).
Proof. exact (MK_COMB (@lem5477493 _70591 _70590) (@lem5477491 _70590 _70591)). Qed.
Lemma lem5477495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477496 (_70591 : int) : (term93 _70591) = (term150 _70591).
Proof. exact (MK_COMB (@lem5477495) (@lem5477391 _70591)). Qed.
Lemma lem5477497 (_70590 : int) (_70591 : int) : (term118 _70591 _70590) = (term164 _70590 _70591).
Proof. exact (MK_COMB (@lem5477496 _70591) (@lem5477494 _70590 _70591)). Qed.
Lemma lem5477498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477499 (_70590 : int) : (term93 _70590) = (term150 _70590).
Proof. exact (MK_COMB (@lem5477498) (@lem5477378 _70590)). Qed.
Lemma lem5477500 (_70590 : int) (_70591 : int) : (term122 _70591 _70590) = (term165 _70590 _70591).
Proof. exact (MK_COMB (@lem5477499 _70590) (@lem5477497 _70590 _70591)). Qed.
Lemma lem5477501 (_70590 : int) (_70591 : int) : (term123 _70591 _70590) = (term165 _70590 _70591).
Proof. exact (TRANS (@lem5477365 _70591 _70590) (@lem5477500 _70590 _70591)). Qed.
Lemma lem5477505 (t : Prop) : (term166 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5477581 (_70590 : int) (_70591 : int) : (term167 _70590 _70591) = (term165 _70590 _70591).
Proof. exact (@lem5477505 (term165 _70590 _70591)). Qed.
Lemma lem5477582 (_70590 : int) : (term133 _70590) = (term168 _70590).
Proof. exact (@lem1988287 (real_of_int _70590) term130). Qed.
Lemma lem5477588 (_70590 : int) : (term169 _70590) = (term170 _70590).
Proof. exact (@lem1982792 (real_of_int _70590) term130). Qed.
Lemma lem5477590 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5477591 : term130 = term172.
Proof. exact (@lem5477590 (NUMERAL 0)). Qed.
Lemma lem5477593 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5477594 : term175 = term176.
Proof. exact (@lem5477593 term144). Qed.
Lemma lem5477595 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5477596 : term177 = term178.
Proof. exact (MK_COMB (@lem5477595) (@lem5477594)). Qed.
Lemma lem5477597 : term179 = term180.
Proof. exact (MK_COMB (@lem5477596) (@lem5477591)). Qed.
Lemma lem5477598 : term180 = term181.
Proof. exact (@lem1981613 term175 term130 term143 term143). Qed.
Lemma lem5477600 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5477601 : term184 = term185.
Proof. exact (@lem5477600 term144 term144). Qed.
Lemma lem5477602 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477603 : term187 = term144.
Proof. exact (EQ_MP (@lem5477602) (@lem940073)). Qed.
Lemma lem5477604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477605 : term185 = term143.
Proof. exact (MK_COMB (@lem5477604) (@lem5477603)). Qed.
Lemma lem5477606 : term184 = term143.
Proof. exact (TRANS (@lem5477601) (@lem5477605)). Qed.
Lemma lem5477608 (x : nat) : (term188 x) = term130.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5477609 : term179 = term130.
Proof. exact (@lem5477608 term144). Qed.
Lemma lem5477610 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5477611 : term189 = term190.
Proof. exact (MK_COMB (@lem5477610) (@lem5477609)). Qed.
Lemma lem5477612 : term181 = term172.
Proof. exact (MK_COMB (@lem5477611) (@lem5477606)). Qed.
Lemma lem5477613 : term180 = term172.
Proof. exact (TRANS (@lem5477598) (@lem5477612)). Qed.
Lemma lem5477614 : term179 = term172.
Proof. exact (TRANS (@lem5477597) (@lem5477613)). Qed.
Lemma lem5477616 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5477617 : term172 = term130.
Proof. exact (@lem5477616 term130). Qed.
Lemma lem5477618 : term179 = term130.
Proof. exact (TRANS (@lem5477614) (@lem5477617)). Qed.
Lemma lem5477619 (_70590 : int) : (term145 _70590) = (term145 _70590).
Proof. exact (eq_refl (term145 _70590)). Qed.
Lemma lem5477620 (_70590 : int) : (term170 _70590) = (term192 _70590).
Proof. exact (MK_COMB (@lem5477619 _70590) (@lem5477618)). Qed.
Lemma lem5477621 (_70590 : int) : (term192 _70590) = (real_of_int _70590).
Proof. exact (@lem1982723 (real_of_int _70590)). Qed.
Lemma lem5477622 (_70590 : int) : (term170 _70590) = (real_of_int _70590).
Proof. exact (TRANS (@lem5477620 _70590) (@lem5477621 _70590)). Qed.
Lemma lem5477624 (_70590 : int) : (term169 _70590) = (real_of_int _70590).
Proof. exact (TRANS (@lem5477588 _70590) (@lem5477622 _70590)). Qed.
Lemma lem5477625 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5477626 (_70590 : int) : (term193 _70590) = (term194 _70590).
Proof. exact (MK_COMB (@lem5477625) (@lem5477624 _70590)). Qed.
Lemma lem5477627 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5477628 (_70590 : int) : (term168 _70590) = (term195 _70590).
Proof. exact (MK_COMB (@lem5477626 _70590) (@lem5477627)). Qed.
Lemma lem5477629 (_70590 : int) : (term133 _70590) = (term195 _70590).
Proof. exact (TRANS (@lem5477582 _70590) (@lem5477628 _70590)). Qed.
Lemma lem5477630 (_70591 : int) : (term133 _70591) = (term168 _70591).
Proof. exact (@lem1988287 (real_of_int _70591) term130). Qed.
Lemma lem5477636 (_70591 : int) : (term169 _70591) = (term170 _70591).
Proof. exact (@lem1982792 (real_of_int _70591) term130). Qed.
Lemma lem5477638 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5477639 : term130 = term172.
Proof. exact (@lem5477638 (NUMERAL 0)). Qed.
Lemma lem5477641 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5477642 : term175 = term176.
Proof. exact (@lem5477641 term144). Qed.
Lemma lem5477643 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5477644 : term177 = term178.
Proof. exact (MK_COMB (@lem5477643) (@lem5477642)). Qed.
Lemma lem5477645 : term179 = term180.
Proof. exact (MK_COMB (@lem5477644) (@lem5477639)). Qed.
Lemma lem5477646 : term180 = term181.
Proof. exact (@lem1981613 term175 term130 term143 term143). Qed.
Lemma lem5477648 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5477649 : term184 = term185.
Proof. exact (@lem5477648 term144 term144). Qed.
Lemma lem5477650 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477651 : term187 = term144.
Proof. exact (EQ_MP (@lem5477650) (@lem940073)). Qed.
Lemma lem5477652 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477653 : term185 = term143.
Proof. exact (MK_COMB (@lem5477652) (@lem5477651)). Qed.
Lemma lem5477654 : term184 = term143.
Proof. exact (TRANS (@lem5477649) (@lem5477653)). Qed.
Lemma lem5477656 (x : nat) : (term188 x) = term130.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5477657 : term179 = term130.
Proof. exact (@lem5477656 term144). Qed.
Lemma lem5477658 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5477659 : term189 = term190.
Proof. exact (MK_COMB (@lem5477658) (@lem5477657)). Qed.
Lemma lem5477660 : term181 = term172.
Proof. exact (MK_COMB (@lem5477659) (@lem5477654)). Qed.
Lemma lem5477661 : term180 = term172.
Proof. exact (TRANS (@lem5477646) (@lem5477660)). Qed.
Lemma lem5477662 : term179 = term172.
Proof. exact (TRANS (@lem5477645) (@lem5477661)). Qed.
Lemma lem5477664 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5477665 : term172 = term130.
Proof. exact (@lem5477664 term130). Qed.
Lemma lem5477666 : term179 = term130.
Proof. exact (TRANS (@lem5477662) (@lem5477665)). Qed.
Lemma lem5477667 (_70591 : int) : (term145 _70591) = (term145 _70591).
Proof. exact (eq_refl (term145 _70591)). Qed.
Lemma lem5477668 (_70591 : int) : (term170 _70591) = (term192 _70591).
Proof. exact (MK_COMB (@lem5477667 _70591) (@lem5477666)). Qed.
Lemma lem5477669 (_70591 : int) : (term192 _70591) = (real_of_int _70591).
Proof. exact (@lem1982723 (real_of_int _70591)). Qed.
Lemma lem5477670 (_70591 : int) : (term170 _70591) = (real_of_int _70591).
Proof. exact (TRANS (@lem5477668 _70591) (@lem5477669 _70591)). Qed.
Lemma lem5477672 (_70591 : int) : (term169 _70591) = (real_of_int _70591).
Proof. exact (TRANS (@lem5477636 _70591) (@lem5477670 _70591)). Qed.
Lemma lem5477673 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5477674 (_70591 : int) : (term193 _70591) = (term194 _70591).
Proof. exact (MK_COMB (@lem5477673) (@lem5477672 _70591)). Qed.
Lemma lem5477675 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5477676 (_70591 : int) : (term168 _70591) = (term195 _70591).
Proof. exact (MK_COMB (@lem5477674 _70591) (@lem5477675)). Qed.
Lemma lem5477677 (_70591 : int) : (term133 _70591) = (term195 _70591).
Proof. exact (TRANS (@lem5477630 _70591) (@lem5477676 _70591)). Qed.
Lemma lem5477678 (_70591 : int) (_70590 : int) : (term149 _70590 _70591) = (term196 _70591 _70590).
Proof. exact (@lem1988287 (real_of_int _70591) (term146 _70590)). Qed.
Lemma lem5477690 (_70591 : int) (_70590 : int) : (term197 _70591 _70590) = (term198 _70591 _70590).
Proof. exact (@lem1982792 (real_of_int _70591) (term146 _70590)). Qed.
Lemma lem5477691 (_70590 : int) : (term199 _70590) = (term200 _70590).
Proof. exact (@lem1982781 (real_of_int _70590) term175 term143). Qed.
Lemma lem5477693 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5477694 : term143 = term201.
Proof. exact (@lem5477693 term144). Qed.
Lemma lem5477696 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5477697 : term175 = term176.
Proof. exact (@lem5477696 term144). Qed.
Lemma lem5477698 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5477699 : term177 = term178.
Proof. exact (MK_COMB (@lem5477698) (@lem5477697)). Qed.
Lemma lem5477700 : term202 = term203.
Proof. exact (MK_COMB (@lem5477699) (@lem5477694)). Qed.
Lemma lem5477701 : term203 = term204.
Proof. exact (@lem1981613 term175 term143 term143 term143). Qed.
Lemma lem5477703 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5477704 : term184 = term185.
Proof. exact (@lem5477703 term144 term144). Qed.
Lemma lem5477705 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477706 : term187 = term144.
Proof. exact (EQ_MP (@lem5477705) (@lem940073)). Qed.
Lemma lem5477707 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477708 : term185 = term143.
Proof. exact (MK_COMB (@lem5477707) (@lem5477706)). Qed.
Lemma lem5477709 : term184 = term143.
Proof. exact (TRANS (@lem5477704) (@lem5477708)). Qed.
Lemma lem5477711 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5477712 : term202 = term207.
Proof. exact (@lem5477711 term144 term144). Qed.
Lemma lem5477713 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477714 : term187 = term144.
Proof. exact (EQ_MP (@lem5477713) (@lem940073)). Qed.
Lemma lem5477715 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477716 : term185 = term143.
Proof. exact (MK_COMB (@lem5477715) (@lem5477714)). Qed.
Lemma lem5477717 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5477718 : term207 = term175.
Proof. exact (MK_COMB (@lem5477717) (@lem5477716)). Qed.
Lemma lem5477719 : term202 = term175.
Proof. exact (TRANS (@lem5477712) (@lem5477718)). Qed.
Lemma lem5477720 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5477721 : term208 = term209.
Proof. exact (MK_COMB (@lem5477720) (@lem5477719)). Qed.
Lemma lem5477722 : term204 = term176.
Proof. exact (MK_COMB (@lem5477721) (@lem5477709)). Qed.
Lemma lem5477723 : term203 = term176.
Proof. exact (TRANS (@lem5477701) (@lem5477722)). Qed.
Lemma lem5477724 : term202 = term176.
Proof. exact (TRANS (@lem5477700) (@lem5477723)). Qed.
Lemma lem5477726 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5477727 : term176 = term175.
Proof. exact (@lem5477726 term175). Qed.
Lemma lem5477728 : term202 = term175.
Proof. exact (TRANS (@lem5477724) (@lem5477727)). Qed.
Lemma lem5477731 (_70590 : int) : (term210 _70590) = (term210 _70590).
Proof. exact (eq_refl (term210 _70590)). Qed.
Lemma lem5477732 (_70590 : int) : (term200 _70590) = (term211 _70590).
Proof. exact (MK_COMB (@lem5477731 _70590) (@lem5477728)). Qed.
Lemma lem5477733 (_70590 : int) : (term199 _70590) = (term211 _70590).
Proof. exact (TRANS (@lem5477691 _70590) (@lem5477732 _70590)). Qed.
Lemma lem5477734 (_70591 : int) : (term145 _70591) = (term145 _70591).
Proof. exact (eq_refl (term145 _70591)). Qed.
Lemma lem5477735 (_70591 : int) (_70590 : int) : (term198 _70591 _70590) = (term212 _70591 _70590).
Proof. exact (MK_COMB (@lem5477734 _70591) (@lem5477733 _70590)). Qed.
Lemma lem5477740 (_70590 : int) (_70591 : int) : (term212 _70591 _70590) = (term213 _70590 _70591).
Proof. exact (@lem1982757 (term214 _70590) (real_of_int _70591) term175). Qed.
Lemma lem5477741 (_70590 : int) (_70591 : int) : (term198 _70591 _70590) = (term213 _70590 _70591).
Proof. exact (TRANS (@lem5477735 _70591 _70590) (@lem5477740 _70590 _70591)). Qed.
Lemma lem5477743 (_70590 : int) (_70591 : int) : (term197 _70591 _70590) = (term213 _70590 _70591).
Proof. exact (TRANS (@lem5477690 _70591 _70590) (@lem5477741 _70590 _70591)). Qed.
Lemma lem5477744 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5477745 (_70590 : int) (_70591 : int) : (term215 _70591 _70590) = (term216 _70590 _70591).
Proof. exact (MK_COMB (@lem5477744) (@lem5477743 _70590 _70591)). Qed.
Lemma lem5477746 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5477747 (_70590 : int) (_70591 : int) : (term196 _70591 _70590) = (term217 _70590 _70591).
Proof. exact (MK_COMB (@lem5477745 _70590 _70591) (@lem5477746)). Qed.
Lemma lem5477748 (_70590 : int) (_70591 : int) : (term149 _70590 _70591) = (term217 _70590 _70591).
Proof. exact (TRANS (@lem5477678 _70591 _70590) (@lem5477747 _70590 _70591)). Qed.
Lemma lem5477749 (_70591 : int) : (term133 _70591) = (term168 _70591).
Proof. exact (@lem1988287 (real_of_int _70591) term130). Qed.
Lemma lem5477755 (_70591 : int) : (term169 _70591) = (term170 _70591).
Proof. exact (@lem1982792 (real_of_int _70591) term130). Qed.
Lemma lem5477757 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5477758 : term130 = term172.
Proof. exact (@lem5477757 (NUMERAL 0)). Qed.
Lemma lem5477760 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5477761 : term175 = term176.
Proof. exact (@lem5477760 term144). Qed.
Lemma lem5477762 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5477763 : term177 = term178.
Proof. exact (MK_COMB (@lem5477762) (@lem5477761)). Qed.
Lemma lem5477764 : term179 = term180.
Proof. exact (MK_COMB (@lem5477763) (@lem5477758)). Qed.
Lemma lem5477765 : term180 = term181.
Proof. exact (@lem1981613 term175 term130 term143 term143). Qed.
Lemma lem5477767 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5477768 : term184 = term185.
Proof. exact (@lem5477767 term144 term144). Qed.
Lemma lem5477769 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477770 : term187 = term144.
Proof. exact (EQ_MP (@lem5477769) (@lem940073)). Qed.
Lemma lem5477771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477772 : term185 = term143.
Proof. exact (MK_COMB (@lem5477771) (@lem5477770)). Qed.
Lemma lem5477773 : term184 = term143.
Proof. exact (TRANS (@lem5477768) (@lem5477772)). Qed.
Lemma lem5477775 (x : nat) : (term188 x) = term130.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5477776 : term179 = term130.
Proof. exact (@lem5477775 term144). Qed.
Lemma lem5477777 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5477778 : term189 = term190.
Proof. exact (MK_COMB (@lem5477777) (@lem5477776)). Qed.
Lemma lem5477779 : term181 = term172.
Proof. exact (MK_COMB (@lem5477778) (@lem5477773)). Qed.
Lemma lem5477780 : term180 = term172.
Proof. exact (TRANS (@lem5477765) (@lem5477779)). Qed.
Lemma lem5477781 : term179 = term172.
Proof. exact (TRANS (@lem5477764) (@lem5477780)). Qed.
Lemma lem5477783 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5477784 : term172 = term130.
Proof. exact (@lem5477783 term130). Qed.
Lemma lem5477785 : term179 = term130.
Proof. exact (TRANS (@lem5477781) (@lem5477784)). Qed.
Lemma lem5477786 (_70591 : int) : (term145 _70591) = (term145 _70591).
Proof. exact (eq_refl (term145 _70591)). Qed.
Lemma lem5477787 (_70591 : int) : (term170 _70591) = (term192 _70591).
Proof. exact (MK_COMB (@lem5477786 _70591) (@lem5477785)). Qed.
Lemma lem5477788 (_70591 : int) : (term192 _70591) = (real_of_int _70591).
Proof. exact (@lem1982723 (real_of_int _70591)). Qed.
Lemma lem5477789 (_70591 : int) : (term170 _70591) = (real_of_int _70591).
Proof. exact (TRANS (@lem5477787 _70591) (@lem5477788 _70591)). Qed.
Lemma lem5477791 (_70591 : int) : (term169 _70591) = (real_of_int _70591).
Proof. exact (TRANS (@lem5477755 _70591) (@lem5477789 _70591)). Qed.
Lemma lem5477792 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5477793 (_70591 : int) : (term193 _70591) = (term194 _70591).
Proof. exact (MK_COMB (@lem5477792) (@lem5477791 _70591)). Qed.
Lemma lem5477794 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5477795 (_70591 : int) : (term168 _70591) = (term195 _70591).
Proof. exact (MK_COMB (@lem5477793 _70591) (@lem5477794)). Qed.
Lemma lem5477796 (_70591 : int) : (term133 _70591) = (term195 _70591).
Proof. exact (TRANS (@lem5477749 _70591) (@lem5477795 _70591)). Qed.
Lemma lem5477797 (_70590 : int) (_70591 : int) : (term125 _70591 _70590) = (term218 _70590 _70591).
Proof. exact (@lem1988287 (real_of_int _70590) (real_of_int _70591)). Qed.
Lemma lem5477810 (_70590 : int) (_70591 : int) : (term219 _70590 _70591) = (term220 _70590 _70591).
Proof. exact (@lem1982792 (real_of_int _70590) (real_of_int _70591)). Qed.
Lemma lem5477811 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5477812 (_70590 : int) (_70591 : int) : (term221 _70590 _70591) = (term222 _70590 _70591).
Proof. exact (MK_COMB (@lem5477811) (@lem5477810 _70590 _70591)). Qed.
Lemma lem5477813 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5477814 (_70590 : int) (_70591 : int) : (term218 _70590 _70591) = (term223 _70590 _70591).
Proof. exact (MK_COMB (@lem5477812 _70590 _70591) (@lem5477813)). Qed.
Lemma lem5477815 (_70590 : int) (_70591 : int) : (term125 _70591 _70590) = (term223 _70590 _70591).
Proof. exact (TRANS (@lem5477797 _70590 _70591) (@lem5477814 _70590 _70591)). Qed.
Lemma lem5477816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477817 (_70591 : int) : (term150 _70591) = (term224 _70591).
Proof. exact (MK_COMB (@lem5477816) (@lem5477796 _70591)). Qed.
Lemma lem5477818 (_70590 : int) (_70591 : int) : (term151 _70591 _70590) = (term225 _70590 _70591).
Proof. exact (MK_COMB (@lem5477817 _70591) (@lem5477815 _70590 _70591)). Qed.
Lemma lem5477819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477820 (_70590 : int) (_70591 : int) : (term152 _70590 _70591) = (term226 _70590 _70591).
Proof. exact (MK_COMB (@lem5477819) (@lem5477748 _70590 _70591)). Qed.
Lemma lem5477821 (_70590 : int) (_70591 : int) : (term153 _70591 _70590) = (term227 _70590 _70591).
Proof. exact (MK_COMB (@lem5477820 _70590 _70591) (@lem5477818 _70590 _70591)). Qed.
Lemma lem5477822 (_70590 : int) (_70591 : int) : (term125 _70591 _70590) = (term218 _70590 _70591).
Proof. exact (@lem1988287 (real_of_int _70590) (real_of_int _70591)). Qed.
Lemma lem5477835 (_70590 : int) (_70591 : int) : (term219 _70590 _70591) = (term220 _70590 _70591).
Proof. exact (@lem1982792 (real_of_int _70590) (real_of_int _70591)). Qed.
Lemma lem5477836 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5477837 (_70590 : int) (_70591 : int) : (term221 _70590 _70591) = (term222 _70590 _70591).
Proof. exact (MK_COMB (@lem5477836) (@lem5477835 _70590 _70591)). Qed.
Lemma lem5477838 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5477839 (_70590 : int) (_70591 : int) : (term218 _70590 _70591) = (term223 _70590 _70591).
Proof. exact (MK_COMB (@lem5477837 _70590 _70591) (@lem5477838)). Qed.
Lemma lem5477840 (_70590 : int) (_70591 : int) : (term125 _70591 _70590) = (term223 _70590 _70591).
Proof. exact (TRANS (@lem5477822 _70590 _70591) (@lem5477839 _70590 _70591)). Qed.
Lemma lem5477841 (_70591 : int) : (term156 _70591) = (term228 _70591).
Proof. exact (@lem1988287 term130 (term146 _70591)). Qed.
Lemma lem5477853 (_70591 : int) : (term229 _70591) = (term230 _70591).
Proof. exact (@lem1982792 term130 (term146 _70591)). Qed.
Lemma lem5477854 (_70591 : int) : (term199 _70591) = (term200 _70591).
Proof. exact (@lem1982781 (real_of_int _70591) term175 term143). Qed.
Lemma lem5477856 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5477857 : term143 = term201.
Proof. exact (@lem5477856 term144). Qed.
Lemma lem5477859 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5477860 : term175 = term176.
Proof. exact (@lem5477859 term144). Qed.
Lemma lem5477861 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5477862 : term177 = term178.
Proof. exact (MK_COMB (@lem5477861) (@lem5477860)). Qed.
Lemma lem5477863 : term202 = term203.
Proof. exact (MK_COMB (@lem5477862) (@lem5477857)). Qed.
Lemma lem5477864 : term203 = term204.
Proof. exact (@lem1981613 term175 term143 term143 term143). Qed.
Lemma lem5477866 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5477867 : term184 = term185.
Proof. exact (@lem5477866 term144 term144). Qed.
Lemma lem5477868 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477869 : term187 = term144.
Proof. exact (EQ_MP (@lem5477868) (@lem940073)). Qed.
Lemma lem5477870 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477871 : term185 = term143.
Proof. exact (MK_COMB (@lem5477870) (@lem5477869)). Qed.
Lemma lem5477872 : term184 = term143.
Proof. exact (TRANS (@lem5477867) (@lem5477871)). Qed.
Lemma lem5477874 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5477875 : term202 = term207.
Proof. exact (@lem5477874 term144 term144). Qed.
Lemma lem5477876 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477877 : term187 = term144.
Proof. exact (EQ_MP (@lem5477876) (@lem940073)). Qed.
Lemma lem5477878 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477879 : term185 = term143.
Proof. exact (MK_COMB (@lem5477878) (@lem5477877)). Qed.
Lemma lem5477880 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5477881 : term207 = term175.
Proof. exact (MK_COMB (@lem5477880) (@lem5477879)). Qed.
Lemma lem5477882 : term202 = term175.
Proof. exact (TRANS (@lem5477875) (@lem5477881)). Qed.
Lemma lem5477883 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5477884 : term208 = term209.
Proof. exact (MK_COMB (@lem5477883) (@lem5477882)). Qed.
Lemma lem5477885 : term204 = term176.
Proof. exact (MK_COMB (@lem5477884) (@lem5477872)). Qed.
Lemma lem5477886 : term203 = term176.
Proof. exact (TRANS (@lem5477864) (@lem5477885)). Qed.
Lemma lem5477887 : term202 = term176.
Proof. exact (TRANS (@lem5477863) (@lem5477886)). Qed.
Lemma lem5477889 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5477890 : term176 = term175.
Proof. exact (@lem5477889 term175). Qed.
Lemma lem5477891 : term202 = term175.
Proof. exact (TRANS (@lem5477887) (@lem5477890)). Qed.
Lemma lem5477894 (_70591 : int) : (term210 _70591) = (term210 _70591).
Proof. exact (eq_refl (term210 _70591)). Qed.
Lemma lem5477895 (_70591 : int) : (term200 _70591) = (term211 _70591).
Proof. exact (MK_COMB (@lem5477894 _70591) (@lem5477891)). Qed.
Lemma lem5477896 (_70591 : int) : (term199 _70591) = (term211 _70591).
Proof. exact (TRANS (@lem5477854 _70591) (@lem5477895 _70591)). Qed.
Lemma lem5477897 : term231 = term231.
Proof. exact (eq_refl term231). Qed.
Lemma lem5477898 (_70591 : int) : (term230 _70591) = (term232 _70591).
Proof. exact (MK_COMB (@lem5477897) (@lem5477896 _70591)). Qed.
Lemma lem5477899 (_70591 : int) : (term232 _70591) = (term211 _70591).
Proof. exact (@lem1982721 (term211 _70591)). Qed.
Lemma lem5477900 (_70591 : int) : (term230 _70591) = (term211 _70591).
Proof. exact (TRANS (@lem5477898 _70591) (@lem5477899 _70591)). Qed.
Lemma lem5477902 (_70591 : int) : (term229 _70591) = (term211 _70591).
Proof. exact (TRANS (@lem5477853 _70591) (@lem5477900 _70591)). Qed.
Lemma lem5477903 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5477904 (_70591 : int) : (term233 _70591) = (term234 _70591).
Proof. exact (MK_COMB (@lem5477903) (@lem5477902 _70591)). Qed.
Lemma lem5477905 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5477906 (_70591 : int) : (term228 _70591) = (term235 _70591).
Proof. exact (MK_COMB (@lem5477904 _70591) (@lem5477905)). Qed.
Lemma lem5477907 (_70591 : int) : (term156 _70591) = (term235 _70591).
Proof. exact (TRANS (@lem5477841 _70591) (@lem5477906 _70591)). Qed.
Lemma lem5477908 (_70591 : int) (_70590 : int) : (term149 _70590 _70591) = (term196 _70591 _70590).
Proof. exact (@lem1988287 (real_of_int _70591) (term146 _70590)). Qed.
Lemma lem5477920 (_70591 : int) (_70590 : int) : (term197 _70591 _70590) = (term198 _70591 _70590).
Proof. exact (@lem1982792 (real_of_int _70591) (term146 _70590)). Qed.
Lemma lem5477921 (_70590 : int) : (term199 _70590) = (term200 _70590).
Proof. exact (@lem1982781 (real_of_int _70590) term175 term143). Qed.
Lemma lem5477923 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5477924 : term143 = term201.
Proof. exact (@lem5477923 term144). Qed.
Lemma lem5477926 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5477927 : term175 = term176.
Proof. exact (@lem5477926 term144). Qed.
Lemma lem5477928 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5477929 : term177 = term178.
Proof. exact (MK_COMB (@lem5477928) (@lem5477927)). Qed.
Lemma lem5477930 : term202 = term203.
Proof. exact (MK_COMB (@lem5477929) (@lem5477924)). Qed.
Lemma lem5477931 : term203 = term204.
Proof. exact (@lem1981613 term175 term143 term143 term143). Qed.
Lemma lem5477933 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5477934 : term184 = term185.
Proof. exact (@lem5477933 term144 term144). Qed.
Lemma lem5477935 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477936 : term187 = term144.
Proof. exact (EQ_MP (@lem5477935) (@lem940073)). Qed.
Lemma lem5477937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477938 : term185 = term143.
Proof. exact (MK_COMB (@lem5477937) (@lem5477936)). Qed.
Lemma lem5477939 : term184 = term143.
Proof. exact (TRANS (@lem5477934) (@lem5477938)). Qed.
Lemma lem5477941 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5477942 : term202 = term207.
Proof. exact (@lem5477941 term144 term144). Qed.
Lemma lem5477943 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5477944 : term187 = term144.
Proof. exact (EQ_MP (@lem5477943) (@lem940073)). Qed.
Lemma lem5477945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5477946 : term185 = term143.
Proof. exact (MK_COMB (@lem5477945) (@lem5477944)). Qed.
Lemma lem5477947 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5477948 : term207 = term175.
Proof. exact (MK_COMB (@lem5477947) (@lem5477946)). Qed.
Lemma lem5477949 : term202 = term175.
Proof. exact (TRANS (@lem5477942) (@lem5477948)). Qed.
Lemma lem5477950 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5477951 : term208 = term209.
Proof. exact (MK_COMB (@lem5477950) (@lem5477949)). Qed.
Lemma lem5477952 : term204 = term176.
Proof. exact (MK_COMB (@lem5477951) (@lem5477939)). Qed.
Lemma lem5477953 : term203 = term176.
Proof. exact (TRANS (@lem5477931) (@lem5477952)). Qed.
Lemma lem5477954 : term202 = term176.
Proof. exact (TRANS (@lem5477930) (@lem5477953)). Qed.
Lemma lem5477956 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5477957 : term176 = term175.
Proof. exact (@lem5477956 term175). Qed.
Lemma lem5477958 : term202 = term175.
Proof. exact (TRANS (@lem5477954) (@lem5477957)). Qed.
Lemma lem5477961 (_70590 : int) : (term210 _70590) = (term210 _70590).
Proof. exact (eq_refl (term210 _70590)). Qed.
Lemma lem5477962 (_70590 : int) : (term200 _70590) = (term211 _70590).
Proof. exact (MK_COMB (@lem5477961 _70590) (@lem5477958)). Qed.
Lemma lem5477963 (_70590 : int) : (term199 _70590) = (term211 _70590).
Proof. exact (TRANS (@lem5477921 _70590) (@lem5477962 _70590)). Qed.
Lemma lem5477964 (_70591 : int) : (term145 _70591) = (term145 _70591).
Proof. exact (eq_refl (term145 _70591)). Qed.
Lemma lem5477965 (_70591 : int) (_70590 : int) : (term198 _70591 _70590) = (term212 _70591 _70590).
Proof. exact (MK_COMB (@lem5477964 _70591) (@lem5477963 _70590)). Qed.
Lemma lem5477970 (_70590 : int) (_70591 : int) : (term212 _70591 _70590) = (term213 _70590 _70591).
Proof. exact (@lem1982757 (term214 _70590) (real_of_int _70591) term175). Qed.
Lemma lem5477971 (_70590 : int) (_70591 : int) : (term198 _70591 _70590) = (term213 _70590 _70591).
Proof. exact (TRANS (@lem5477965 _70591 _70590) (@lem5477970 _70590 _70591)). Qed.
Lemma lem5477973 (_70590 : int) (_70591 : int) : (term197 _70591 _70590) = (term213 _70590 _70591).
Proof. exact (TRANS (@lem5477920 _70591 _70590) (@lem5477971 _70590 _70591)). Qed.
Lemma lem5477974 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5477975 (_70590 : int) (_70591 : int) : (term215 _70591 _70590) = (term216 _70590 _70591).
Proof. exact (MK_COMB (@lem5477974) (@lem5477973 _70590 _70591)). Qed.
Lemma lem5477976 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5477977 (_70590 : int) (_70591 : int) : (term196 _70591 _70590) = (term217 _70590 _70591).
Proof. exact (MK_COMB (@lem5477975 _70590 _70591) (@lem5477976)). Qed.
Lemma lem5477978 (_70590 : int) (_70591 : int) : (term149 _70590 _70591) = (term217 _70590 _70591).
Proof. exact (TRANS (@lem5477908 _70591 _70590) (@lem5477977 _70590 _70591)). Qed.
Lemma lem5477979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5477980 (_70591 : int) : (term158 _70591) = (term236 _70591).
Proof. exact (MK_COMB (@lem5477979) (@lem5477907 _70591)). Qed.
Lemma lem5477981 (_70590 : int) (_70591 : int) : (term159 _70590 _70591) = (term237 _70590 _70591).
Proof. exact (MK_COMB (@lem5477980 _70591) (@lem5477978 _70590 _70591)). Qed.
Lemma lem5477982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477983 (_70590 : int) (_70591 : int) : (term160 _70591 _70590) = (term238 _70590 _70591).
Proof. exact (MK_COMB (@lem5477982) (@lem5477840 _70590 _70591)). Qed.
Lemma lem5477984 (_70590 : int) (_70591 : int) : (term161 _70590 _70591) = (term239 _70590 _70591).
Proof. exact (MK_COMB (@lem5477983 _70590 _70591) (@lem5477981 _70590 _70591)). Qed.
Lemma lem5477985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5477986 (_70590 : int) (_70591 : int) : (term162 _70591 _70590) = (term240 _70590 _70591).
Proof. exact (MK_COMB (@lem5477985) (@lem5477821 _70590 _70591)). Qed.
Lemma lem5477987 (_70590 : int) (_70591 : int) : (term163 _70590 _70591) = (term241 _70590 _70591).
Proof. exact (MK_COMB (@lem5477986 _70590 _70591) (@lem5477984 _70590 _70591)). Qed.
Lemma lem5477988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477989 (_70591 : int) : (term150 _70591) = (term224 _70591).
Proof. exact (MK_COMB (@lem5477988) (@lem5477677 _70591)). Qed.
Lemma lem5477990 (_70590 : int) (_70591 : int) : (term164 _70590 _70591) = (term242 _70590 _70591).
Proof. exact (MK_COMB (@lem5477989 _70591) (@lem5477987 _70590 _70591)). Qed.
Lemma lem5477991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5477992 (_70590 : int) : (term150 _70590) = (term224 _70590).
Proof. exact (MK_COMB (@lem5477991) (@lem5477629 _70590)). Qed.
Lemma lem5477993 (_70590 : int) (_70591 : int) : (term165 _70590 _70591) = (term243 _70590 _70591).
Proof. exact (MK_COMB (@lem5477992 _70590) (@lem5477990 _70590 _70591)). Qed.
Lemma lem5478000 (_70590 : int) (_70591 : int) : (term167 _70590 _70591) = (term243 _70590 _70591).
Proof. exact (TRANS (@lem5477581 _70590 _70591) (@lem5477993 _70590 _70591)). Qed.
Lemma lem5478017 (_70590 : int) (_70591 : int) : (term239 _70590 _70591) = (term244 _70590 _70591).
Proof. exact (@lem19158 (term235 _70591) (term223 _70590 _70591) (term217 _70590 _70591)). Qed.
Lemma lem5478032 (_70590 : int) (_70591 : int) : (term240 _70590 _70591) = (term240 _70590 _70591).
Proof. exact (eq_refl (term240 _70590 _70591)). Qed.
Lemma lem5478033 (_70590 : int) (_70591 : int) : (term241 _70590 _70591) = (term245 _70590 _70591).
Proof. exact (MK_COMB (@lem5478032 _70590 _70591) (@lem5478017 _70590 _70591)). Qed.
Lemma lem5478036 (_70591 : int) : (term224 _70591) = (term224 _70591).
Proof. exact (eq_refl (term224 _70591)). Qed.
Lemma lem5478037 (_70590 : int) (_70591 : int) : (term242 _70590 _70591) = (term246 _70590 _70591).
Proof. exact (MK_COMB (@lem5478036 _70591) (@lem5478033 _70590 _70591)). Qed.
Lemma lem5478038 (_70590 : int) (_70591 : int) : (term246 _70590 _70591) = (term247 _70590 _70591).
Proof. exact (@lem19158 (term227 _70590 _70591) (term195 _70591) (term244 _70590 _70591)). Qed.
Lemma lem5478045 (_70590 : int) (_70591 : int) : (term248 _70590 _70591) = (term249 _70590 _70591).
Proof. exact (@lem19158 (term250 _70590 _70591) (term195 _70591) (term251 _70590 _70591)). Qed.
Lemma lem5478048 (_70590 : int) (_70591 : int) : (term252 _70590 _70591) = (term252 _70590 _70591).
Proof. exact (eq_refl (term252 _70590 _70591)). Qed.
Lemma lem5478049 (_70590 : int) (_70591 : int) : (term247 _70590 _70591) = (term253 _70590 _70591).
Proof. exact (MK_COMB (@lem5478048 _70590 _70591) (@lem5478045 _70590 _70591)). Qed.
Lemma lem5478050 (_70590 : int) (_70591 : int) : (term246 _70590 _70591) = (term253 _70590 _70591).
Proof. exact (TRANS (@lem5478038 _70590 _70591) (@lem5478049 _70590 _70591)). Qed.
Lemma lem5478051 (_70590 : int) (_70591 : int) : (term242 _70590 _70591) = (term253 _70590 _70591).
Proof. exact (TRANS (@lem5478037 _70590 _70591) (@lem5478050 _70590 _70591)). Qed.
Lemma lem5478054 (_70590 : int) : (term224 _70590) = (term224 _70590).
Proof. exact (eq_refl (term224 _70590)). Qed.
Lemma lem5478055 (_70590 : int) (_70591 : int) : (term243 _70590 _70591) = (term254 _70590 _70591).
Proof. exact (MK_COMB (@lem5478054 _70590) (@lem5478051 _70590 _70591)). Qed.
Lemma lem5478056 (_70590 : int) (_70591 : int) : (term254 _70590 _70591) = (term255 _70590 _70591).
Proof. exact (@lem19158 (term256 _70590 _70591) (term195 _70590) (term249 _70590 _70591)). Qed.
Lemma lem5478063 (_70590 : int) (_70591 : int) : (term257 _70590 _70591) = (term258 _70590 _70591).
Proof. exact (@lem19158 (term259 _70590 _70591) (term195 _70590) (term260 _70590 _70591)). Qed.
Lemma lem5478066 (_70590 : int) (_70591 : int) : (term261 _70590 _70591) = (term261 _70590 _70591).
Proof. exact (eq_refl (term261 _70590 _70591)). Qed.
Lemma lem5478067 (_70590 : int) (_70591 : int) : (term255 _70590 _70591) = (term262 _70590 _70591).
Proof. exact (MK_COMB (@lem5478066 _70590 _70591) (@lem5478063 _70590 _70591)). Qed.
Lemma lem5478068 (_70590 : int) (_70591 : int) : (term254 _70590 _70591) = (term262 _70590 _70591).
Proof. exact (TRANS (@lem5478056 _70590 _70591) (@lem5478067 _70590 _70591)). Qed.
Lemma lem5478069 (_70590 : int) (_70591 : int) : (term243 _70590 _70591) = (term262 _70590 _70591).
Proof. exact (TRANS (@lem5478055 _70590 _70591) (@lem5478068 _70590 _70591)). Qed.
Lemma lem5478070 (_70590 : int) (_70591 : int) : (term167 _70590 _70591) = (term262 _70590 _70591).
Proof. exact (TRANS (@lem5478000 _70590 _70591) (@lem5478069 _70590 _70591)). Qed.
Lemma lem5478086 (_70590 : int) (_70591 : int) (h1 : term262 _70590 _70591) : term262 _70590 _70591.
Proof. exact (h1). Qed.
Lemma lem5478087 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term263 _70590 _70591.
Proof. exact (h1). Qed.
Lemma lem5478088 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term256 _70590 _70591.
Proof. exact (proj2 (@lem5478087 _70590 _70591 h1)). Qed.
Lemma lem5478090 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term227 _70590 _70591.
Proof. exact (proj2 (@lem5478088 _70590 _70591 h1)). Qed.
Lemma lem5478092 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term225 _70590 _70591.
Proof. exact (proj2 (@lem5478090 _70590 _70591 h1)). Qed.
Lemma lem5478093 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term217 _70590 _70591.
Proof. exact (proj1 (@lem5478090 _70590 _70591 h1)). Qed.
Lemma lem5478094 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term223 _70590 _70591.
Proof. exact (proj2 (@lem5478092 _70590 _70591 h1)). Qed.
Lemma lem5478097 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5478098 : term264 = term265.
Proof. exact (@lem5478097 term130 term143). Qed.
Lemma lem5478100 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478101 : term143 = term201.
Proof. exact (@lem5478100 term144). Qed.
Lemma lem5478103 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478104 : term130 = term172.
Proof. exact (@lem5478103 (NUMERAL 0)). Qed.
Lemma lem5478105 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478106 : term266 = term267.
Proof. exact (MK_COMB (@lem5478105) (@lem5478104)). Qed.
Lemma lem5478107 : term265 = term268.
Proof. exact (MK_COMB (@lem5478106) (@lem5478101)). Qed.
Lemma lem5478108 : term269.
Proof. exact (@lem1980255 term130 term143 term143 term143). Qed.
Lemma lem5478110 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478111 : term265 = term271.
Proof. exact (@lem5478110 (NUMERAL 0) term144). Qed.
Lemma lem5478112 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478113 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478114 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478113 h1) (fun h1 : term271 = True => @lem5478112)). Qed.
Lemma lem5478115 : term271 = True.
Proof. exact (EQ_MP (@lem5478114) (@lem5478112)). Qed.
Lemma lem5478116 : term265 = True.
Proof. exact (TRANS (@lem5478111) (@lem5478115)). Qed.
Lemma lem5478117 : True = term265.
Proof. exact (SYM (@lem5478116)). Qed.
Lemma lem5478118 : term265.
Proof. exact (EQ_MP (@lem5478117) (@lem0)). Qed.
Lemma lem5478119 : term273.
Proof. exact (@lem5478108 (@lem5478118)). Qed.
Lemma lem5478121 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478122 : term265 = term271.
Proof. exact (@lem5478121 (NUMERAL 0) term144). Qed.
Lemma lem5478123 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478124 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478125 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478124 h1) (fun h1 : term271 = True => @lem5478123)). Qed.
Lemma lem5478126 : term271 = True.
Proof. exact (EQ_MP (@lem5478125) (@lem5478123)). Qed.
Lemma lem5478127 : term265 = True.
Proof. exact (TRANS (@lem5478122) (@lem5478126)). Qed.
Lemma lem5478128 : True = term265.
Proof. exact (SYM (@lem5478127)). Qed.
Lemma lem5478129 : term265.
Proof. exact (EQ_MP (@lem5478128) (@lem0)). Qed.
Lemma lem5478130 : term268 = term274.
Proof. exact (@lem5478119 (@lem5478129)). Qed.
Lemma lem5478132 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478133 : term184 = term185.
Proof. exact (@lem5478132 term144 term144). Qed.
Lemma lem5478134 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478135 : term187 = term144.
Proof. exact (EQ_MP (@lem5478134) (@lem940073)). Qed.
Lemma lem5478136 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478137 : term185 = term143.
Proof. exact (MK_COMB (@lem5478136) (@lem5478135)). Qed.
Lemma lem5478138 : term184 = term143.
Proof. exact (TRANS (@lem5478133) (@lem5478137)). Qed.
Lemma lem5478140 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478141 : term276 = term130.
Proof. exact (@lem5478140 term144). Qed.
Lemma lem5478142 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478143 : term277 = term266.
Proof. exact (MK_COMB (@lem5478142) (@lem5478141)). Qed.
Lemma lem5478144 : term274 = term265.
Proof. exact (MK_COMB (@lem5478143) (@lem5478138)). Qed.
Lemma lem5478146 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478147 : term265 = term271.
Proof. exact (@lem5478146 (NUMERAL 0) term144). Qed.
Lemma lem5478148 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478149 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478150 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478149 h1) (fun h1 : term271 = True => @lem5478148)). Qed.
Lemma lem5478151 : term271 = True.
Proof. exact (EQ_MP (@lem5478150) (@lem5478148)). Qed.
Lemma lem5478152 : term265 = True.
Proof. exact (TRANS (@lem5478147) (@lem5478151)). Qed.
Lemma lem5478153 : term274 = True.
Proof. exact (TRANS (@lem5478144) (@lem5478152)). Qed.
Lemma lem5478154 : term268 = True.
Proof. exact (TRANS (@lem5478130) (@lem5478153)). Qed.
Lemma lem5478155 : term265 = True.
Proof. exact (TRANS (@lem5478107) (@lem5478154)). Qed.
Lemma lem5478156 : term264 = True.
Proof. exact (TRANS (@lem5478098) (@lem5478155)). Qed.
Lemma lem5478157 : True = term264.
Proof. exact (SYM (@lem5478156)). Qed.
Lemma lem5478158 : term264.
Proof. exact (EQ_MP (@lem5478157) (@lem0)). Qed.
Lemma lem5478159 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term278 _70590 _70591.
Proof. exact (conj (@lem5478158) (@lem5478094 _70590 _70591 h1)). Qed.
Lemma lem5478161 (x : real) (y : real) : term279 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5478162 (_70590 : int) (_70591 : int) : term280 _70590 _70591.
Proof. exact (@lem5478161 term143 (term220 _70590 _70591)). Qed.
Lemma lem5478163 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term281 _70590 _70591.
Proof. exact (@lem5478162 _70590 _70591 (@lem5478159 _70590 _70591 h1)). Qed.
Lemma lem5478164 (_70590 : int) (_70591 : int) : (term282 _70590 _70591) = (term220 _70590 _70591).
Proof. exact (@lem1982733 (term220 _70590 _70591)). Qed.
Lemma lem5478165 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5478166 (_70590 : int) (_70591 : int) : (term283 _70590 _70591) = (term222 _70590 _70591).
Proof. exact (MK_COMB (@lem5478165) (@lem5478164 _70590 _70591)). Qed.
Lemma lem5478167 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5478168 (_70590 : int) (_70591 : int) : (term281 _70590 _70591) = (term223 _70590 _70591).
Proof. exact (MK_COMB (@lem5478166 _70590 _70591) (@lem5478167)). Qed.
Lemma lem5478169 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term223 _70590 _70591.
Proof. exact (EQ_MP (@lem5478168 _70590 _70591) (@lem5478163 _70590 _70591 h1)). Qed.
Lemma lem5478171 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5478172 : term264 = term265.
Proof. exact (@lem5478171 term130 term143). Qed.
Lemma lem5478174 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478175 : term143 = term201.
Proof. exact (@lem5478174 term144). Qed.
Lemma lem5478177 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478178 : term130 = term172.
Proof. exact (@lem5478177 (NUMERAL 0)). Qed.
Lemma lem5478179 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478180 : term266 = term267.
Proof. exact (MK_COMB (@lem5478179) (@lem5478178)). Qed.
Lemma lem5478181 : term265 = term268.
Proof. exact (MK_COMB (@lem5478180) (@lem5478175)). Qed.
Lemma lem5478182 : term269.
Proof. exact (@lem1980255 term130 term143 term143 term143). Qed.
Lemma lem5478184 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478185 : term265 = term271.
Proof. exact (@lem5478184 (NUMERAL 0) term144). Qed.
Lemma lem5478186 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478187 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478188 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478187 h1) (fun h1 : term271 = True => @lem5478186)). Qed.
Lemma lem5478189 : term271 = True.
Proof. exact (EQ_MP (@lem5478188) (@lem5478186)). Qed.
Lemma lem5478190 : term265 = True.
Proof. exact (TRANS (@lem5478185) (@lem5478189)). Qed.
Lemma lem5478191 : True = term265.
Proof. exact (SYM (@lem5478190)). Qed.
Lemma lem5478192 : term265.
Proof. exact (EQ_MP (@lem5478191) (@lem0)). Qed.
Lemma lem5478193 : term273.
Proof. exact (@lem5478182 (@lem5478192)). Qed.
Lemma lem5478195 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478196 : term265 = term271.
Proof. exact (@lem5478195 (NUMERAL 0) term144). Qed.
Lemma lem5478197 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478198 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478199 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478198 h1) (fun h1 : term271 = True => @lem5478197)). Qed.
Lemma lem5478200 : term271 = True.
Proof. exact (EQ_MP (@lem5478199) (@lem5478197)). Qed.
Lemma lem5478201 : term265 = True.
Proof. exact (TRANS (@lem5478196) (@lem5478200)). Qed.
Lemma lem5478202 : True = term265.
Proof. exact (SYM (@lem5478201)). Qed.
Lemma lem5478203 : term265.
Proof. exact (EQ_MP (@lem5478202) (@lem0)). Qed.
Lemma lem5478204 : term268 = term274.
Proof. exact (@lem5478193 (@lem5478203)). Qed.
Lemma lem5478206 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478207 : term184 = term185.
Proof. exact (@lem5478206 term144 term144). Qed.
Lemma lem5478208 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478209 : term187 = term144.
Proof. exact (EQ_MP (@lem5478208) (@lem940073)). Qed.
Lemma lem5478210 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478211 : term185 = term143.
Proof. exact (MK_COMB (@lem5478210) (@lem5478209)). Qed.
Lemma lem5478212 : term184 = term143.
Proof. exact (TRANS (@lem5478207) (@lem5478211)). Qed.
Lemma lem5478214 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478215 : term276 = term130.
Proof. exact (@lem5478214 term144). Qed.
Lemma lem5478216 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478217 : term277 = term266.
Proof. exact (MK_COMB (@lem5478216) (@lem5478215)). Qed.
Lemma lem5478218 : term274 = term265.
Proof. exact (MK_COMB (@lem5478217) (@lem5478212)). Qed.
Lemma lem5478220 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478221 : term265 = term271.
Proof. exact (@lem5478220 (NUMERAL 0) term144). Qed.
Lemma lem5478222 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478223 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478224 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478223 h1) (fun h1 : term271 = True => @lem5478222)). Qed.
Lemma lem5478225 : term271 = True.
Proof. exact (EQ_MP (@lem5478224) (@lem5478222)). Qed.
Lemma lem5478226 : term265 = True.
Proof. exact (TRANS (@lem5478221) (@lem5478225)). Qed.
Lemma lem5478227 : term274 = True.
Proof. exact (TRANS (@lem5478218) (@lem5478226)). Qed.
Lemma lem5478228 : term268 = True.
Proof. exact (TRANS (@lem5478204) (@lem5478227)). Qed.
Lemma lem5478229 : term265 = True.
Proof. exact (TRANS (@lem5478181) (@lem5478228)). Qed.
Lemma lem5478230 : term264 = True.
Proof. exact (TRANS (@lem5478172) (@lem5478229)). Qed.
Lemma lem5478231 : True = term264.
Proof. exact (SYM (@lem5478230)). Qed.
Lemma lem5478232 : term264.
Proof. exact (EQ_MP (@lem5478231) (@lem0)). Qed.
Lemma lem5478233 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term284 _70590 _70591.
Proof. exact (conj (@lem5478232) (@lem5478093 _70590 _70591 h1)). Qed.
Lemma lem5478235 (x : real) (y : real) : term279 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5478236 (_70590 : int) (_70591 : int) : term285 _70590 _70591.
Proof. exact (@lem5478235 term143 (term213 _70590 _70591)). Qed.
Lemma lem5478237 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term286 _70590 _70591.
Proof. exact (@lem5478236 _70590 _70591 (@lem5478233 _70590 _70591 h1)). Qed.
Lemma lem5478238 (_70590 : int) (_70591 : int) : (term287 _70590 _70591) = (term213 _70590 _70591).
Proof. exact (@lem1982733 (term213 _70590 _70591)). Qed.
Lemma lem5478239 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5478240 (_70590 : int) (_70591 : int) : (term288 _70590 _70591) = (term216 _70590 _70591).
Proof. exact (MK_COMB (@lem5478239) (@lem5478238 _70590 _70591)). Qed.
Lemma lem5478241 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5478242 (_70590 : int) (_70591 : int) : (term286 _70590 _70591) = (term217 _70590 _70591).
Proof. exact (MK_COMB (@lem5478240 _70590 _70591) (@lem5478241)). Qed.
Lemma lem5478243 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term217 _70590 _70591.
Proof. exact (EQ_MP (@lem5478242 _70590 _70591) (@lem5478237 _70590 _70591 h1)). Qed.
Lemma lem5478244 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term289 _70590 _70591.
Proof. exact (conj (@lem5478243 _70590 _70591 h1) (@lem5478169 _70590 _70591 h1)). Qed.
Lemma lem5478246 (x : real) (y : real) : term290 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5478247 (_70590 : int) (_70591 : int) : term291 _70590 _70591.
Proof. exact (@lem5478246 (term213 _70590 _70591) (term220 _70590 _70591)). Qed.
Lemma lem5478248 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term292 _70590 _70591.
Proof. exact (@lem5478247 _70590 _70591 (@lem5478244 _70590 _70591 h1)). Qed.
Lemma lem5478249 (_70590 : int) (_70591 : int) : (term293 _70590 _70591) = (term294 _70590 _70591).
Proof. exact (@lem1982753 (term214 _70590) (real_of_int _70590) (term295 _70591) (term214 _70591)). Qed.
Lemma lem5478250 (_70590 : int) : (term296 _70590) = (term297 _70590).
Proof. exact (@lem1982713 term175 (real_of_int _70590)). Qed.
Lemma lem5478252 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478253 : term143 = term201.
Proof. exact (@lem5478252 term144). Qed.
Lemma lem5478255 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5478256 : term175 = term176.
Proof. exact (@lem5478255 term144). Qed.
Lemma lem5478257 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478258 : term298 = term299.
Proof. exact (MK_COMB (@lem5478257) (@lem5478256)). Qed.
Lemma lem5478259 : term300 = term301.
Proof. exact (MK_COMB (@lem5478258) (@lem5478253)). Qed.
Lemma lem5478260 : term302.
Proof. exact (@lem1981473 term175 term143 term143 term143 term130 term143). Qed.
Lemma lem5478262 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478263 : term265 = term271.
Proof. exact (@lem5478262 (NUMERAL 0) term144). Qed.
Lemma lem5478264 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478265 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478266 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478265 h1) (fun h1 : term271 = True => @lem5478264)). Qed.
Lemma lem5478267 : term271 = True.
Proof. exact (EQ_MP (@lem5478266) (@lem5478264)). Qed.
Lemma lem5478268 : term265 = True.
Proof. exact (TRANS (@lem5478263) (@lem5478267)). Qed.
Lemma lem5478269 : True = term265.
Proof. exact (SYM (@lem5478268)). Qed.
Lemma lem5478270 : term265.
Proof. exact (EQ_MP (@lem5478269) (@lem0)). Qed.
Lemma lem5478271 : term303.
Proof. exact (@lem5478260 (@lem5478270)). Qed.
Lemma lem5478273 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478274 : term265 = term271.
Proof. exact (@lem5478273 (NUMERAL 0) term144). Qed.
Lemma lem5478275 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478276 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478277 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478276 h1) (fun h1 : term271 = True => @lem5478275)). Qed.
Lemma lem5478278 : term271 = True.
Proof. exact (EQ_MP (@lem5478277) (@lem5478275)). Qed.
Lemma lem5478279 : term265 = True.
Proof. exact (TRANS (@lem5478274) (@lem5478278)). Qed.
Lemma lem5478280 : True = term265.
Proof. exact (SYM (@lem5478279)). Qed.
Lemma lem5478281 : term265.
Proof. exact (EQ_MP (@lem5478280) (@lem0)). Qed.
Lemma lem5478282 : term304.
Proof. exact (@lem5478271 (@lem5478281)). Qed.
Lemma lem5478284 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478285 : term265 = term271.
Proof. exact (@lem5478284 (NUMERAL 0) term144). Qed.
Lemma lem5478286 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478287 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478288 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478287 h1) (fun h1 : term271 = True => @lem5478286)). Qed.
Lemma lem5478289 : term271 = True.
Proof. exact (EQ_MP (@lem5478288) (@lem5478286)). Qed.
Lemma lem5478290 : term265 = True.
Proof. exact (TRANS (@lem5478285) (@lem5478289)). Qed.
Lemma lem5478291 : True = term265.
Proof. exact (SYM (@lem5478290)). Qed.
Lemma lem5478292 : term265.
Proof. exact (EQ_MP (@lem5478291) (@lem0)). Qed.
Lemma lem5478293 : term305.
Proof. exact (@lem5478282 (@lem5478292)). Qed.
Lemma lem5478295 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478296 : term184 = term185.
Proof. exact (@lem5478295 term144 term144). Qed.
Lemma lem5478297 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478298 : term187 = term144.
Proof. exact (EQ_MP (@lem5478297) (@lem940073)). Qed.
Lemma lem5478299 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478300 : term185 = term143.
Proof. exact (MK_COMB (@lem5478299) (@lem5478298)). Qed.
Lemma lem5478301 : term184 = term143.
Proof. exact (TRANS (@lem5478296) (@lem5478300)). Qed.
Lemma lem5478303 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5478304 : term202 = term207.
Proof. exact (@lem5478303 term144 term144). Qed.
Lemma lem5478305 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478306 : term187 = term144.
Proof. exact (EQ_MP (@lem5478305) (@lem940073)). Qed.
Lemma lem5478307 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478308 : term185 = term143.
Proof. exact (MK_COMB (@lem5478307) (@lem5478306)). Qed.
Lemma lem5478309 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5478310 : term207 = term175.
Proof. exact (MK_COMB (@lem5478309) (@lem5478308)). Qed.
Lemma lem5478311 : term202 = term175.
Proof. exact (TRANS (@lem5478304) (@lem5478310)). Qed.
Lemma lem5478312 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478313 : term306 = term298.
Proof. exact (MK_COMB (@lem5478312) (@lem5478311)). Qed.
Lemma lem5478314 : term307 = term300.
Proof. exact (MK_COMB (@lem5478313) (@lem5478301)). Qed.
Lemma lem5478316 (m : nat) : (term308 m) = term130.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5478317 : term300 = term130.
Proof. exact (@lem5478316 term144). Qed.
Lemma lem5478318 : term307 = term130.
Proof. exact (TRANS (@lem5478314) (@lem5478317)). Qed.
Lemma lem5478319 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5478320 : term309 = term310.
Proof. exact (MK_COMB (@lem5478319) (@lem5478318)). Qed.
Lemma lem5478321 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5478322 : term311 = term276.
Proof. exact (MK_COMB (@lem5478320) (@lem5478321)). Qed.
Lemma lem5478324 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478325 : term276 = term130.
Proof. exact (@lem5478324 term144). Qed.
Lemma lem5478326 : term311 = term130.
Proof. exact (TRANS (@lem5478322) (@lem5478325)). Qed.
Lemma lem5478328 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478329 : term184 = term185.
Proof. exact (@lem5478328 term144 term144). Qed.
Lemma lem5478330 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478331 : term187 = term144.
Proof. exact (EQ_MP (@lem5478330) (@lem940073)). Qed.
Lemma lem5478332 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478333 : term185 = term143.
Proof. exact (MK_COMB (@lem5478332) (@lem5478331)). Qed.
Lemma lem5478334 : term184 = term143.
Proof. exact (TRANS (@lem5478329) (@lem5478333)). Qed.
Lemma lem5478335 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem5478336 : term312 = term276.
Proof. exact (MK_COMB (@lem5478335) (@lem5478334)). Qed.
Lemma lem5478338 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478339 : term276 = term130.
Proof. exact (@lem5478338 term144). Qed.
Lemma lem5478340 : term312 = term130.
Proof. exact (TRANS (@lem5478336) (@lem5478339)). Qed.
Lemma lem5478341 : term130 = term312.
Proof. exact (SYM (@lem5478340)). Qed.
Lemma lem5478342 : term311 = term312.
Proof. exact (TRANS (@lem5478326) (@lem5478341)). Qed.
Lemma lem5478343 : term301 = term172.
Proof. exact (@lem5478293 (@lem5478342)). Qed.
Lemma lem5478344 : term300 = term172.
Proof. exact (TRANS (@lem5478259) (@lem5478343)). Qed.
Lemma lem5478346 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5478347 : term172 = term130.
Proof. exact (@lem5478346 term130). Qed.
Lemma lem5478348 : term300 = term130.
Proof. exact (TRANS (@lem5478344) (@lem5478347)). Qed.
Lemma lem5478349 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5478350 : term313 = term310.
Proof. exact (MK_COMB (@lem5478349) (@lem5478348)). Qed.
Lemma lem5478351 (_70590 : int) : (real_of_int _70590) = (real_of_int _70590).
Proof. exact (eq_refl (real_of_int _70590)). Qed.
Lemma lem5478352 (_70590 : int) : (term297 _70590) = (term314 _70590).
Proof. exact (MK_COMB (@lem5478350) (@lem5478351 _70590)). Qed.
Lemma lem5478353 (_70590 : int) : (term296 _70590) = (term314 _70590).
Proof. exact (TRANS (@lem5478250 _70590) (@lem5478352 _70590)). Qed.
Lemma lem5478354 (_70590 : int) : (term314 _70590) = term130.
Proof. exact (@lem1982719 (real_of_int _70590)). Qed.
Lemma lem5478355 (_70590 : int) : (term296 _70590) = term130.
Proof. exact (TRANS (@lem5478353 _70590) (@lem5478354 _70590)). Qed.
Lemma lem5478356 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478357 (_70590 : int) : (term315 _70590) = term231.
Proof. exact (MK_COMB (@lem5478356) (@lem5478355 _70590)). Qed.
Lemma lem5478358 (_70591 : int) : (term316 _70591) = (term317 _70591).
Proof. exact (@lem1982759 (real_of_int _70591) (term214 _70591) term175). Qed.
Lemma lem5478359 (_70591 : int) : (term318 _70591) = (term297 _70591).
Proof. exact (@lem1982715 term175 (real_of_int _70591)). Qed.
Lemma lem5478361 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478362 : term143 = term201.
Proof. exact (@lem5478361 term144). Qed.
Lemma lem5478364 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5478365 : term175 = term176.
Proof. exact (@lem5478364 term144). Qed.
Lemma lem5478366 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478367 : term298 = term299.
Proof. exact (MK_COMB (@lem5478366) (@lem5478365)). Qed.
Lemma lem5478368 : term300 = term301.
Proof. exact (MK_COMB (@lem5478367) (@lem5478362)). Qed.
Lemma lem5478369 : term302.
Proof. exact (@lem1981473 term175 term143 term143 term143 term130 term143). Qed.
Lemma lem5478371 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478372 : term265 = term271.
Proof. exact (@lem5478371 (NUMERAL 0) term144). Qed.
Lemma lem5478373 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478374 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478375 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478374 h1) (fun h1 : term271 = True => @lem5478373)). Qed.
Lemma lem5478376 : term271 = True.
Proof. exact (EQ_MP (@lem5478375) (@lem5478373)). Qed.
Lemma lem5478377 : term265 = True.
Proof. exact (TRANS (@lem5478372) (@lem5478376)). Qed.
Lemma lem5478378 : True = term265.
Proof. exact (SYM (@lem5478377)). Qed.
Lemma lem5478379 : term265.
Proof. exact (EQ_MP (@lem5478378) (@lem0)). Qed.
Lemma lem5478380 : term303.
Proof. exact (@lem5478369 (@lem5478379)). Qed.
Lemma lem5478382 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478383 : term265 = term271.
Proof. exact (@lem5478382 (NUMERAL 0) term144). Qed.
Lemma lem5478384 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478385 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478386 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478385 h1) (fun h1 : term271 = True => @lem5478384)). Qed.
Lemma lem5478387 : term271 = True.
Proof. exact (EQ_MP (@lem5478386) (@lem5478384)). Qed.
Lemma lem5478388 : term265 = True.
Proof. exact (TRANS (@lem5478383) (@lem5478387)). Qed.
Lemma lem5478389 : True = term265.
Proof. exact (SYM (@lem5478388)). Qed.
Lemma lem5478390 : term265.
Proof. exact (EQ_MP (@lem5478389) (@lem0)). Qed.
Lemma lem5478391 : term304.
Proof. exact (@lem5478380 (@lem5478390)). Qed.
Lemma lem5478393 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478394 : term265 = term271.
Proof. exact (@lem5478393 (NUMERAL 0) term144). Qed.
Lemma lem5478395 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478396 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478397 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478396 h1) (fun h1 : term271 = True => @lem5478395)). Qed.
Lemma lem5478398 : term271 = True.
Proof. exact (EQ_MP (@lem5478397) (@lem5478395)). Qed.
Lemma lem5478399 : term265 = True.
Proof. exact (TRANS (@lem5478394) (@lem5478398)). Qed.
Lemma lem5478400 : True = term265.
Proof. exact (SYM (@lem5478399)). Qed.
Lemma lem5478401 : term265.
Proof. exact (EQ_MP (@lem5478400) (@lem0)). Qed.
Lemma lem5478402 : term305.
Proof. exact (@lem5478391 (@lem5478401)). Qed.
Lemma lem5478404 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478405 : term184 = term185.
Proof. exact (@lem5478404 term144 term144). Qed.
Lemma lem5478406 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478407 : term187 = term144.
Proof. exact (EQ_MP (@lem5478406) (@lem940073)). Qed.
Lemma lem5478408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478409 : term185 = term143.
Proof. exact (MK_COMB (@lem5478408) (@lem5478407)). Qed.
Lemma lem5478410 : term184 = term143.
Proof. exact (TRANS (@lem5478405) (@lem5478409)). Qed.
Lemma lem5478412 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5478413 : term202 = term207.
Proof. exact (@lem5478412 term144 term144). Qed.
Lemma lem5478414 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478415 : term187 = term144.
Proof. exact (EQ_MP (@lem5478414) (@lem940073)). Qed.
Lemma lem5478416 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478417 : term185 = term143.
Proof. exact (MK_COMB (@lem5478416) (@lem5478415)). Qed.
Lemma lem5478418 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5478419 : term207 = term175.
Proof. exact (MK_COMB (@lem5478418) (@lem5478417)). Qed.
Lemma lem5478420 : term202 = term175.
Proof. exact (TRANS (@lem5478413) (@lem5478419)). Qed.
Lemma lem5478421 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478422 : term306 = term298.
Proof. exact (MK_COMB (@lem5478421) (@lem5478420)). Qed.
Lemma lem5478423 : term307 = term300.
Proof. exact (MK_COMB (@lem5478422) (@lem5478410)). Qed.
Lemma lem5478425 (m : nat) : (term308 m) = term130.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5478426 : term300 = term130.
Proof. exact (@lem5478425 term144). Qed.
Lemma lem5478427 : term307 = term130.
Proof. exact (TRANS (@lem5478423) (@lem5478426)). Qed.
Lemma lem5478428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5478429 : term309 = term310.
Proof. exact (MK_COMB (@lem5478428) (@lem5478427)). Qed.
Lemma lem5478430 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5478431 : term311 = term276.
Proof. exact (MK_COMB (@lem5478429) (@lem5478430)). Qed.
Lemma lem5478433 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478434 : term276 = term130.
Proof. exact (@lem5478433 term144). Qed.
Lemma lem5478435 : term311 = term130.
Proof. exact (TRANS (@lem5478431) (@lem5478434)). Qed.
Lemma lem5478437 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478438 : term184 = term185.
Proof. exact (@lem5478437 term144 term144). Qed.
Lemma lem5478439 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478440 : term187 = term144.
Proof. exact (EQ_MP (@lem5478439) (@lem940073)). Qed.
Lemma lem5478441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478442 : term185 = term143.
Proof. exact (MK_COMB (@lem5478441) (@lem5478440)). Qed.
Lemma lem5478443 : term184 = term143.
Proof. exact (TRANS (@lem5478438) (@lem5478442)). Qed.
Lemma lem5478444 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem5478445 : term312 = term276.
Proof. exact (MK_COMB (@lem5478444) (@lem5478443)). Qed.
Lemma lem5478447 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478448 : term276 = term130.
Proof. exact (@lem5478447 term144). Qed.
Lemma lem5478449 : term312 = term130.
Proof. exact (TRANS (@lem5478445) (@lem5478448)). Qed.
Lemma lem5478450 : term130 = term312.
Proof. exact (SYM (@lem5478449)). Qed.
Lemma lem5478451 : term311 = term312.
Proof. exact (TRANS (@lem5478435) (@lem5478450)). Qed.
Lemma lem5478452 : term301 = term172.
Proof. exact (@lem5478402 (@lem5478451)). Qed.
Lemma lem5478453 : term300 = term172.
Proof. exact (TRANS (@lem5478368) (@lem5478452)). Qed.
Lemma lem5478455 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5478456 : term172 = term130.
Proof. exact (@lem5478455 term130). Qed.
Lemma lem5478457 : term300 = term130.
Proof. exact (TRANS (@lem5478453) (@lem5478456)). Qed.
Lemma lem5478458 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5478459 : term313 = term310.
Proof. exact (MK_COMB (@lem5478458) (@lem5478457)). Qed.
Lemma lem5478460 (_70591 : int) : (real_of_int _70591) = (real_of_int _70591).
Proof. exact (eq_refl (real_of_int _70591)). Qed.
Lemma lem5478461 (_70591 : int) : (term297 _70591) = (term314 _70591).
Proof. exact (MK_COMB (@lem5478459) (@lem5478460 _70591)). Qed.
Lemma lem5478462 (_70591 : int) : (term318 _70591) = (term314 _70591).
Proof. exact (TRANS (@lem5478359 _70591) (@lem5478461 _70591)). Qed.
Lemma lem5478463 (_70591 : int) : (term314 _70591) = term130.
Proof. exact (@lem1982719 (real_of_int _70591)). Qed.
Lemma lem5478464 (_70591 : int) : (term318 _70591) = term130.
Proof. exact (TRANS (@lem5478462 _70591) (@lem5478463 _70591)). Qed.
Lemma lem5478465 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478466 (_70591 : int) : (term319 _70591) = term231.
Proof. exact (MK_COMB (@lem5478465) (@lem5478464 _70591)). Qed.
Lemma lem5478467 : term175 = term175.
Proof. exact (eq_refl term175). Qed.
Lemma lem5478468 (_70591 : int) : (term317 _70591) = term320.
Proof. exact (MK_COMB (@lem5478466 _70591) (@lem5478467)). Qed.
Lemma lem5478469 (_70591 : int) : (term316 _70591) = term320.
Proof. exact (TRANS (@lem5478358 _70591) (@lem5478468 _70591)). Qed.
Lemma lem5478470 : term320 = term175.
Proof. exact (@lem1982721 term175). Qed.
Lemma lem5478471 (_70591 : int) : (term316 _70591) = term175.
Proof. exact (TRANS (@lem5478469 _70591) (@lem5478470)). Qed.
Lemma lem5478472 (_70590 : int) (_70591 : int) : (term294 _70590 _70591) = term320.
Proof. exact (MK_COMB (@lem5478357 _70590) (@lem5478471 _70591)). Qed.
Lemma lem5478473 (_70590 : int) (_70591 : int) : (term293 _70590 _70591) = term320.
Proof. exact (TRANS (@lem5478249 _70590 _70591) (@lem5478472 _70590 _70591)). Qed.
Lemma lem5478474 : term320 = term175.
Proof. exact (@lem1982721 term175). Qed.
Lemma lem5478475 (_70590 : int) (_70591 : int) : (term293 _70590 _70591) = term175.
Proof. exact (TRANS (@lem5478473 _70590 _70591) (@lem5478474)). Qed.
Lemma lem5478476 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5478477 (_70590 : int) (_70591 : int) : (term321 _70590 _70591) = term322.
Proof. exact (MK_COMB (@lem5478476) (@lem5478475 _70590 _70591)). Qed.
Lemma lem5478478 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5478479 (_70590 : int) (_70591 : int) : (term292 _70590 _70591) = term323.
Proof. exact (MK_COMB (@lem5478477 _70590 _70591) (@lem5478478)). Qed.
Lemma lem5478480 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : term323.
Proof. exact (EQ_MP (@lem5478479 _70590 _70591) (@lem5478248 _70590 _70591 h1)). Qed.
Lemma lem5478482 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5478483 : term323 = term324.
Proof. exact (@lem5478482 term130 term175). Qed.
Lemma lem5478485 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5478486 : term175 = term176.
Proof. exact (@lem5478485 term144). Qed.
Lemma lem5478488 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478489 : term130 = term172.
Proof. exact (@lem5478488 (NUMERAL 0)). Qed.
Lemma lem5478490 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5478491 : term132 = term325.
Proof. exact (MK_COMB (@lem5478490) (@lem5478489)). Qed.
Lemma lem5478492 : term324 = term326.
Proof. exact (MK_COMB (@lem5478491) (@lem5478486)). Qed.
Lemma lem5478493 : term327.
Proof. exact (@lem1980026 term130 term143 term175 term143). Qed.
Lemma lem5478495 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478496 : term265 = term271.
Proof. exact (@lem5478495 (NUMERAL 0) term144). Qed.
Lemma lem5478497 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478498 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478499 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478498 h1) (fun h1 : term271 = True => @lem5478497)). Qed.
Lemma lem5478500 : term271 = True.
Proof. exact (EQ_MP (@lem5478499) (@lem5478497)). Qed.
Lemma lem5478501 : term265 = True.
Proof. exact (TRANS (@lem5478496) (@lem5478500)). Qed.
Lemma lem5478502 : True = term265.
Proof. exact (SYM (@lem5478501)). Qed.
Lemma lem5478503 : term265.
Proof. exact (EQ_MP (@lem5478502) (@lem0)). Qed.
Lemma lem5478504 : term328.
Proof. exact (@lem5478493 (@lem5478503)). Qed.
Lemma lem5478506 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478507 : term265 = term271.
Proof. exact (@lem5478506 (NUMERAL 0) term144). Qed.
Lemma lem5478508 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478509 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478510 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478509 h1) (fun h1 : term271 = True => @lem5478508)). Qed.
Lemma lem5478511 : term271 = True.
Proof. exact (EQ_MP (@lem5478510) (@lem5478508)). Qed.
Lemma lem5478512 : term265 = True.
Proof. exact (TRANS (@lem5478507) (@lem5478511)). Qed.
Lemma lem5478513 : True = term265.
Proof. exact (SYM (@lem5478512)). Qed.
Lemma lem5478514 : term265.
Proof. exact (EQ_MP (@lem5478513) (@lem0)). Qed.
Lemma lem5478515 : term326 = term329.
Proof. exact (@lem5478504 (@lem5478514)). Qed.
Lemma lem5478517 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5478518 : term202 = term207.
Proof. exact (@lem5478517 term144 term144). Qed.
Lemma lem5478519 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478520 : term187 = term144.
Proof. exact (EQ_MP (@lem5478519) (@lem940073)). Qed.
Lemma lem5478521 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478522 : term185 = term143.
Proof. exact (MK_COMB (@lem5478521) (@lem5478520)). Qed.
Lemma lem5478523 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5478524 : term207 = term175.
Proof. exact (MK_COMB (@lem5478523) (@lem5478522)). Qed.
Lemma lem5478525 : term202 = term175.
Proof. exact (TRANS (@lem5478518) (@lem5478524)). Qed.
Lemma lem5478527 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478528 : term276 = term130.
Proof. exact (@lem5478527 term144). Qed.
Lemma lem5478529 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5478530 : term330 = term132.
Proof. exact (MK_COMB (@lem5478529) (@lem5478528)). Qed.
Lemma lem5478531 : term329 = term324.
Proof. exact (MK_COMB (@lem5478530) (@lem5478525)). Qed.
Lemma lem5478533 (m : nat) (n : nat) : (term331 m n) = (term332 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5478534 : term324 = term333.
Proof. exact (@lem5478533 (NUMERAL 0) term144). Qed.
Lemma lem5478535 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478536 (h1 : term272 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5478537 : (term272 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478536 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5478535)). Qed.
Lemma lem5478538 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5478537) (@lem5478535)). Qed.
Lemma lem5478539 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5478540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5478541 : term334 = (and True).
Proof. exact (MK_COMB (@lem5478540) (@lem5478539)). Qed.
Lemma lem5478542 : term333 = (True /\ False).
Proof. exact (MK_COMB (@lem5478541) (@lem5478538)). Qed.
Lemma lem5478544 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5478545 : term333 = False.
Proof. exact (TRANS (@lem5478542) (@lem5478544)). Qed.
Lemma lem5478546 : term324 = False.
Proof. exact (TRANS (@lem5478534) (@lem5478545)). Qed.
Lemma lem5478547 : term329 = False.
Proof. exact (TRANS (@lem5478531) (@lem5478546)). Qed.
Lemma lem5478548 : term326 = False.
Proof. exact (TRANS (@lem5478515) (@lem5478547)). Qed.
Lemma lem5478549 : term324 = False.
Proof. exact (TRANS (@lem5478492) (@lem5478548)). Qed.
Lemma lem5478550 : term323 = False.
Proof. exact (TRANS (@lem5478483) (@lem5478549)). Qed.
Lemma lem5478551 (_70590 : int) (_70591 : int) (h1 : term263 _70590 _70591) : False.
Proof. exact (EQ_MP (@lem5478550) (@lem5478480 _70590 _70591 h1)). Qed.
Lemma lem5478552 (_70590 : int) (_70591 : int) (h1 : term258 _70590 _70591) : term258 _70590 _70591.
Proof. exact (h1). Qed.
Lemma lem5478553 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term335 _70590 _70591.
Proof. exact (h1). Qed.
Lemma lem5478554 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term259 _70590 _70591.
Proof. exact (proj2 (@lem5478553 _70590 _70591 h1)). Qed.
Lemma lem5478556 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term250 _70590 _70591.
Proof. exact (proj2 (@lem5478554 _70590 _70591 h1)). Qed.
Lemma lem5478557 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term195 _70591.
Proof. exact (proj1 (@lem5478554 _70590 _70591 h1)). Qed.
Lemma lem5478558 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term235 _70591.
Proof. exact (proj2 (@lem5478556 _70590 _70591 h1)). Qed.
Lemma lem5478561 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5478562 : term264 = term265.
Proof. exact (@lem5478561 term130 term143). Qed.
Lemma lem5478564 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478565 : term143 = term201.
Proof. exact (@lem5478564 term144). Qed.
Lemma lem5478567 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478568 : term130 = term172.
Proof. exact (@lem5478567 (NUMERAL 0)). Qed.
Lemma lem5478569 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478570 : term266 = term267.
Proof. exact (MK_COMB (@lem5478569) (@lem5478568)). Qed.
Lemma lem5478571 : term265 = term268.
Proof. exact (MK_COMB (@lem5478570) (@lem5478565)). Qed.
Lemma lem5478572 : term269.
Proof. exact (@lem1980255 term130 term143 term143 term143). Qed.
Lemma lem5478574 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478575 : term265 = term271.
Proof. exact (@lem5478574 (NUMERAL 0) term144). Qed.
Lemma lem5478576 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478577 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478578 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478577 h1) (fun h1 : term271 = True => @lem5478576)). Qed.
Lemma lem5478579 : term271 = True.
Proof. exact (EQ_MP (@lem5478578) (@lem5478576)). Qed.
Lemma lem5478580 : term265 = True.
Proof. exact (TRANS (@lem5478575) (@lem5478579)). Qed.
Lemma lem5478581 : True = term265.
Proof. exact (SYM (@lem5478580)). Qed.
Lemma lem5478582 : term265.
Proof. exact (EQ_MP (@lem5478581) (@lem0)). Qed.
Lemma lem5478583 : term273.
Proof. exact (@lem5478572 (@lem5478582)). Qed.
Lemma lem5478585 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478586 : term265 = term271.
Proof. exact (@lem5478585 (NUMERAL 0) term144). Qed.
Lemma lem5478587 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478588 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478589 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478588 h1) (fun h1 : term271 = True => @lem5478587)). Qed.
Lemma lem5478590 : term271 = True.
Proof. exact (EQ_MP (@lem5478589) (@lem5478587)). Qed.
Lemma lem5478591 : term265 = True.
Proof. exact (TRANS (@lem5478586) (@lem5478590)). Qed.
Lemma lem5478592 : True = term265.
Proof. exact (SYM (@lem5478591)). Qed.
Lemma lem5478593 : term265.
Proof. exact (EQ_MP (@lem5478592) (@lem0)). Qed.
Lemma lem5478594 : term268 = term274.
Proof. exact (@lem5478583 (@lem5478593)). Qed.
Lemma lem5478596 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478597 : term184 = term185.
Proof. exact (@lem5478596 term144 term144). Qed.
Lemma lem5478598 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478599 : term187 = term144.
Proof. exact (EQ_MP (@lem5478598) (@lem940073)). Qed.
Lemma lem5478600 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478601 : term185 = term143.
Proof. exact (MK_COMB (@lem5478600) (@lem5478599)). Qed.
Lemma lem5478602 : term184 = term143.
Proof. exact (TRANS (@lem5478597) (@lem5478601)). Qed.
Lemma lem5478604 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478605 : term276 = term130.
Proof. exact (@lem5478604 term144). Qed.
Lemma lem5478606 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478607 : term277 = term266.
Proof. exact (MK_COMB (@lem5478606) (@lem5478605)). Qed.
Lemma lem5478608 : term274 = term265.
Proof. exact (MK_COMB (@lem5478607) (@lem5478602)). Qed.
Lemma lem5478610 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478611 : term265 = term271.
Proof. exact (@lem5478610 (NUMERAL 0) term144). Qed.
Lemma lem5478612 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478613 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478614 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478613 h1) (fun h1 : term271 = True => @lem5478612)). Qed.
Lemma lem5478615 : term271 = True.
Proof. exact (EQ_MP (@lem5478614) (@lem5478612)). Qed.
Lemma lem5478616 : term265 = True.
Proof. exact (TRANS (@lem5478611) (@lem5478615)). Qed.
Lemma lem5478617 : term274 = True.
Proof. exact (TRANS (@lem5478608) (@lem5478616)). Qed.
Lemma lem5478618 : term268 = True.
Proof. exact (TRANS (@lem5478594) (@lem5478617)). Qed.
Lemma lem5478619 : term265 = True.
Proof. exact (TRANS (@lem5478571) (@lem5478618)). Qed.
Lemma lem5478620 : term264 = True.
Proof. exact (TRANS (@lem5478562) (@lem5478619)). Qed.
Lemma lem5478621 : True = term264.
Proof. exact (SYM (@lem5478620)). Qed.
Lemma lem5478622 : term264.
Proof. exact (EQ_MP (@lem5478621) (@lem0)). Qed.
Lemma lem5478623 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term336 _70591.
Proof. exact (conj (@lem5478622) (@lem5478557 _70590 _70591 h1)). Qed.
Lemma lem5478625 (x : real) (y : real) : term279 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5478626 (_70591 : int) : term337 _70591.
Proof. exact (@lem5478625 term143 (real_of_int _70591)). Qed.
Lemma lem5478627 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term338 _70591.
Proof. exact (@lem5478626 _70591 (@lem5478623 _70590 _70591 h1)). Qed.
Lemma lem5478628 (_70591 : int) : (term339 _70591) = (real_of_int _70591).
Proof. exact (@lem1982733 (real_of_int _70591)). Qed.
Lemma lem5478629 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5478630 (_70591 : int) : (term340 _70591) = (term194 _70591).
Proof. exact (MK_COMB (@lem5478629) (@lem5478628 _70591)). Qed.
Lemma lem5478631 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5478632 (_70591 : int) : (term338 _70591) = (term195 _70591).
Proof. exact (MK_COMB (@lem5478630 _70591) (@lem5478631)). Qed.
Lemma lem5478633 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term195 _70591.
Proof. exact (EQ_MP (@lem5478632 _70591) (@lem5478627 _70590 _70591 h1)). Qed.
Lemma lem5478635 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5478636 : term264 = term265.
Proof. exact (@lem5478635 term130 term143). Qed.
Lemma lem5478638 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478639 : term143 = term201.
Proof. exact (@lem5478638 term144). Qed.
Lemma lem5478641 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478642 : term130 = term172.
Proof. exact (@lem5478641 (NUMERAL 0)). Qed.
Lemma lem5478643 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478644 : term266 = term267.
Proof. exact (MK_COMB (@lem5478643) (@lem5478642)). Qed.
Lemma lem5478645 : term265 = term268.
Proof. exact (MK_COMB (@lem5478644) (@lem5478639)). Qed.
Lemma lem5478646 : term269.
Proof. exact (@lem1980255 term130 term143 term143 term143). Qed.
Lemma lem5478648 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478649 : term265 = term271.
Proof. exact (@lem5478648 (NUMERAL 0) term144). Qed.
Lemma lem5478650 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478651 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478652 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478651 h1) (fun h1 : term271 = True => @lem5478650)). Qed.
Lemma lem5478653 : term271 = True.
Proof. exact (EQ_MP (@lem5478652) (@lem5478650)). Qed.
Lemma lem5478654 : term265 = True.
Proof. exact (TRANS (@lem5478649) (@lem5478653)). Qed.
Lemma lem5478655 : True = term265.
Proof. exact (SYM (@lem5478654)). Qed.
Lemma lem5478656 : term265.
Proof. exact (EQ_MP (@lem5478655) (@lem0)). Qed.
Lemma lem5478657 : term273.
Proof. exact (@lem5478646 (@lem5478656)). Qed.
Lemma lem5478659 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478660 : term265 = term271.
Proof. exact (@lem5478659 (NUMERAL 0) term144). Qed.
Lemma lem5478661 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478662 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478663 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478662 h1) (fun h1 : term271 = True => @lem5478661)). Qed.
Lemma lem5478664 : term271 = True.
Proof. exact (EQ_MP (@lem5478663) (@lem5478661)). Qed.
Lemma lem5478665 : term265 = True.
Proof. exact (TRANS (@lem5478660) (@lem5478664)). Qed.
Lemma lem5478666 : True = term265.
Proof. exact (SYM (@lem5478665)). Qed.
Lemma lem5478667 : term265.
Proof. exact (EQ_MP (@lem5478666) (@lem0)). Qed.
Lemma lem5478668 : term268 = term274.
Proof. exact (@lem5478657 (@lem5478667)). Qed.
Lemma lem5478670 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478671 : term184 = term185.
Proof. exact (@lem5478670 term144 term144). Qed.
Lemma lem5478672 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478673 : term187 = term144.
Proof. exact (EQ_MP (@lem5478672) (@lem940073)). Qed.
Lemma lem5478674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478675 : term185 = term143.
Proof. exact (MK_COMB (@lem5478674) (@lem5478673)). Qed.
Lemma lem5478676 : term184 = term143.
Proof. exact (TRANS (@lem5478671) (@lem5478675)). Qed.
Lemma lem5478678 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478679 : term276 = term130.
Proof. exact (@lem5478678 term144). Qed.
Lemma lem5478680 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478681 : term277 = term266.
Proof. exact (MK_COMB (@lem5478680) (@lem5478679)). Qed.
Lemma lem5478682 : term274 = term265.
Proof. exact (MK_COMB (@lem5478681) (@lem5478676)). Qed.
Lemma lem5478684 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478685 : term265 = term271.
Proof. exact (@lem5478684 (NUMERAL 0) term144). Qed.
Lemma lem5478686 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478687 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478688 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478687 h1) (fun h1 : term271 = True => @lem5478686)). Qed.
Lemma lem5478689 : term271 = True.
Proof. exact (EQ_MP (@lem5478688) (@lem5478686)). Qed.
Lemma lem5478690 : term265 = True.
Proof. exact (TRANS (@lem5478685) (@lem5478689)). Qed.
Lemma lem5478691 : term274 = True.
Proof. exact (TRANS (@lem5478682) (@lem5478690)). Qed.
Lemma lem5478692 : term268 = True.
Proof. exact (TRANS (@lem5478668) (@lem5478691)). Qed.
Lemma lem5478693 : term265 = True.
Proof. exact (TRANS (@lem5478645) (@lem5478692)). Qed.
Lemma lem5478694 : term264 = True.
Proof. exact (TRANS (@lem5478636) (@lem5478693)). Qed.
Lemma lem5478695 : True = term264.
Proof. exact (SYM (@lem5478694)). Qed.
Lemma lem5478696 : term264.
Proof. exact (EQ_MP (@lem5478695) (@lem0)). Qed.
Lemma lem5478697 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term341 _70591.
Proof. exact (conj (@lem5478696) (@lem5478558 _70590 _70591 h1)). Qed.
Lemma lem5478699 (x : real) (y : real) : term279 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5478700 (_70591 : int) : term342 _70591.
Proof. exact (@lem5478699 term143 (term211 _70591)). Qed.
Lemma lem5478701 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term343 _70591.
Proof. exact (@lem5478700 _70591 (@lem5478697 _70590 _70591 h1)). Qed.
Lemma lem5478702 (_70591 : int) : (term344 _70591) = (term211 _70591).
Proof. exact (@lem1982733 (term211 _70591)). Qed.
Lemma lem5478703 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5478704 (_70591 : int) : (term345 _70591) = (term234 _70591).
Proof. exact (MK_COMB (@lem5478703) (@lem5478702 _70591)). Qed.
Lemma lem5478705 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5478706 (_70591 : int) : (term343 _70591) = (term235 _70591).
Proof. exact (MK_COMB (@lem5478704 _70591) (@lem5478705)). Qed.
Lemma lem5478707 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term235 _70591.
Proof. exact (EQ_MP (@lem5478706 _70591) (@lem5478701 _70590 _70591 h1)). Qed.
Lemma lem5478708 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term346 _70591.
Proof. exact (conj (@lem5478707 _70590 _70591 h1) (@lem5478633 _70590 _70591 h1)). Qed.
Lemma lem5478710 (x : real) (y : real) : term290 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5478711 (_70591 : int) : term347 _70591.
Proof. exact (@lem5478710 (term211 _70591) (real_of_int _70591)). Qed.
Lemma lem5478712 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term348 _70591.
Proof. exact (@lem5478711 _70591 (@lem5478708 _70590 _70591 h1)). Qed.
Lemma lem5478713 (_70591 : int) : (term349 _70591) = (term350 _70591).
Proof. exact (@lem1982759 (term214 _70591) (real_of_int _70591) term175). Qed.
Lemma lem5478714 (_70591 : int) : (term296 _70591) = (term297 _70591).
Proof. exact (@lem1982713 term175 (real_of_int _70591)). Qed.
Lemma lem5478716 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478717 : term143 = term201.
Proof. exact (@lem5478716 term144). Qed.
Lemma lem5478719 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5478720 : term175 = term176.
Proof. exact (@lem5478719 term144). Qed.
Lemma lem5478721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478722 : term298 = term299.
Proof. exact (MK_COMB (@lem5478721) (@lem5478720)). Qed.
Lemma lem5478723 : term300 = term301.
Proof. exact (MK_COMB (@lem5478722) (@lem5478717)). Qed.
Lemma lem5478724 : term302.
Proof. exact (@lem1981473 term175 term143 term143 term143 term130 term143). Qed.
Lemma lem5478726 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478727 : term265 = term271.
Proof. exact (@lem5478726 (NUMERAL 0) term144). Qed.
Lemma lem5478728 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478729 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478730 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478729 h1) (fun h1 : term271 = True => @lem5478728)). Qed.
Lemma lem5478731 : term271 = True.
Proof. exact (EQ_MP (@lem5478730) (@lem5478728)). Qed.
Lemma lem5478732 : term265 = True.
Proof. exact (TRANS (@lem5478727) (@lem5478731)). Qed.
Lemma lem5478733 : True = term265.
Proof. exact (SYM (@lem5478732)). Qed.
Lemma lem5478734 : term265.
Proof. exact (EQ_MP (@lem5478733) (@lem0)). Qed.
Lemma lem5478735 : term303.
Proof. exact (@lem5478724 (@lem5478734)). Qed.
Lemma lem5478737 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478738 : term265 = term271.
Proof. exact (@lem5478737 (NUMERAL 0) term144). Qed.
Lemma lem5478739 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478740 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478741 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478740 h1) (fun h1 : term271 = True => @lem5478739)). Qed.
Lemma lem5478742 : term271 = True.
Proof. exact (EQ_MP (@lem5478741) (@lem5478739)). Qed.
Lemma lem5478743 : term265 = True.
Proof. exact (TRANS (@lem5478738) (@lem5478742)). Qed.
Lemma lem5478744 : True = term265.
Proof. exact (SYM (@lem5478743)). Qed.
Lemma lem5478745 : term265.
Proof. exact (EQ_MP (@lem5478744) (@lem0)). Qed.
Lemma lem5478746 : term304.
Proof. exact (@lem5478735 (@lem5478745)). Qed.
Lemma lem5478748 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478749 : term265 = term271.
Proof. exact (@lem5478748 (NUMERAL 0) term144). Qed.
Lemma lem5478750 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478751 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478752 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478751 h1) (fun h1 : term271 = True => @lem5478750)). Qed.
Lemma lem5478753 : term271 = True.
Proof. exact (EQ_MP (@lem5478752) (@lem5478750)). Qed.
Lemma lem5478754 : term265 = True.
Proof. exact (TRANS (@lem5478749) (@lem5478753)). Qed.
Lemma lem5478755 : True = term265.
Proof. exact (SYM (@lem5478754)). Qed.
Lemma lem5478756 : term265.
Proof. exact (EQ_MP (@lem5478755) (@lem0)). Qed.
Lemma lem5478757 : term305.
Proof. exact (@lem5478746 (@lem5478756)). Qed.
Lemma lem5478759 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478760 : term184 = term185.
Proof. exact (@lem5478759 term144 term144). Qed.
Lemma lem5478761 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478762 : term187 = term144.
Proof. exact (EQ_MP (@lem5478761) (@lem940073)). Qed.
Lemma lem5478763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478764 : term185 = term143.
Proof. exact (MK_COMB (@lem5478763) (@lem5478762)). Qed.
Lemma lem5478765 : term184 = term143.
Proof. exact (TRANS (@lem5478760) (@lem5478764)). Qed.
Lemma lem5478767 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5478768 : term202 = term207.
Proof. exact (@lem5478767 term144 term144). Qed.
Lemma lem5478769 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478770 : term187 = term144.
Proof. exact (EQ_MP (@lem5478769) (@lem940073)). Qed.
Lemma lem5478771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478772 : term185 = term143.
Proof. exact (MK_COMB (@lem5478771) (@lem5478770)). Qed.
Lemma lem5478773 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5478774 : term207 = term175.
Proof. exact (MK_COMB (@lem5478773) (@lem5478772)). Qed.
Lemma lem5478775 : term202 = term175.
Proof. exact (TRANS (@lem5478768) (@lem5478774)). Qed.
Lemma lem5478776 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478777 : term306 = term298.
Proof. exact (MK_COMB (@lem5478776) (@lem5478775)). Qed.
Lemma lem5478778 : term307 = term300.
Proof. exact (MK_COMB (@lem5478777) (@lem5478765)). Qed.
Lemma lem5478780 (m : nat) : (term308 m) = term130.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5478781 : term300 = term130.
Proof. exact (@lem5478780 term144). Qed.
Lemma lem5478782 : term307 = term130.
Proof. exact (TRANS (@lem5478778) (@lem5478781)). Qed.
Lemma lem5478783 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5478784 : term309 = term310.
Proof. exact (MK_COMB (@lem5478783) (@lem5478782)). Qed.
Lemma lem5478785 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5478786 : term311 = term276.
Proof. exact (MK_COMB (@lem5478784) (@lem5478785)). Qed.
Lemma lem5478788 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478789 : term276 = term130.
Proof. exact (@lem5478788 term144). Qed.
Lemma lem5478790 : term311 = term130.
Proof. exact (TRANS (@lem5478786) (@lem5478789)). Qed.
Lemma lem5478792 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478793 : term184 = term185.
Proof. exact (@lem5478792 term144 term144). Qed.
Lemma lem5478794 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478795 : term187 = term144.
Proof. exact (EQ_MP (@lem5478794) (@lem940073)). Qed.
Lemma lem5478796 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478797 : term185 = term143.
Proof. exact (MK_COMB (@lem5478796) (@lem5478795)). Qed.
Lemma lem5478798 : term184 = term143.
Proof. exact (TRANS (@lem5478793) (@lem5478797)). Qed.
Lemma lem5478799 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem5478800 : term312 = term276.
Proof. exact (MK_COMB (@lem5478799) (@lem5478798)). Qed.
Lemma lem5478802 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478803 : term276 = term130.
Proof. exact (@lem5478802 term144). Qed.
Lemma lem5478804 : term312 = term130.
Proof. exact (TRANS (@lem5478800) (@lem5478803)). Qed.
Lemma lem5478805 : term130 = term312.
Proof. exact (SYM (@lem5478804)). Qed.
Lemma lem5478806 : term311 = term312.
Proof. exact (TRANS (@lem5478790) (@lem5478805)). Qed.
Lemma lem5478807 : term301 = term172.
Proof. exact (@lem5478757 (@lem5478806)). Qed.
Lemma lem5478808 : term300 = term172.
Proof. exact (TRANS (@lem5478723) (@lem5478807)). Qed.
Lemma lem5478810 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5478811 : term172 = term130.
Proof. exact (@lem5478810 term130). Qed.
Lemma lem5478812 : term300 = term130.
Proof. exact (TRANS (@lem5478808) (@lem5478811)). Qed.
Lemma lem5478813 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5478814 : term313 = term310.
Proof. exact (MK_COMB (@lem5478813) (@lem5478812)). Qed.
Lemma lem5478815 (_70591 : int) : (real_of_int _70591) = (real_of_int _70591).
Proof. exact (eq_refl (real_of_int _70591)). Qed.
Lemma lem5478816 (_70591 : int) : (term297 _70591) = (term314 _70591).
Proof. exact (MK_COMB (@lem5478814) (@lem5478815 _70591)). Qed.
Lemma lem5478817 (_70591 : int) : (term296 _70591) = (term314 _70591).
Proof. exact (TRANS (@lem5478714 _70591) (@lem5478816 _70591)). Qed.
Lemma lem5478818 (_70591 : int) : (term314 _70591) = term130.
Proof. exact (@lem1982719 (real_of_int _70591)). Qed.
Lemma lem5478819 (_70591 : int) : (term296 _70591) = term130.
Proof. exact (TRANS (@lem5478817 _70591) (@lem5478818 _70591)). Qed.
Lemma lem5478820 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5478821 (_70591 : int) : (term315 _70591) = term231.
Proof. exact (MK_COMB (@lem5478820) (@lem5478819 _70591)). Qed.
Lemma lem5478822 : term175 = term175.
Proof. exact (eq_refl term175). Qed.
Lemma lem5478823 (_70591 : int) : (term350 _70591) = term320.
Proof. exact (MK_COMB (@lem5478821 _70591) (@lem5478822)). Qed.
Lemma lem5478824 (_70591 : int) : (term349 _70591) = term320.
Proof. exact (TRANS (@lem5478713 _70591) (@lem5478823 _70591)). Qed.
Lemma lem5478825 : term320 = term175.
Proof. exact (@lem1982721 term175). Qed.
Lemma lem5478826 (_70591 : int) : (term349 _70591) = term175.
Proof. exact (TRANS (@lem5478824 _70591) (@lem5478825)). Qed.
Lemma lem5478827 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5478828 (_70591 : int) : (term351 _70591) = term322.
Proof. exact (MK_COMB (@lem5478827) (@lem5478826 _70591)). Qed.
Lemma lem5478829 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5478830 (_70591 : int) : (term348 _70591) = term323.
Proof. exact (MK_COMB (@lem5478828 _70591) (@lem5478829)). Qed.
Lemma lem5478831 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : term323.
Proof. exact (EQ_MP (@lem5478830 _70591) (@lem5478712 _70590 _70591 h1)). Qed.
Lemma lem5478833 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5478834 : term323 = term324.
Proof. exact (@lem5478833 term130 term175). Qed.
Lemma lem5478836 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5478837 : term175 = term176.
Proof. exact (@lem5478836 term144). Qed.
Lemma lem5478839 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478840 : term130 = term172.
Proof. exact (@lem5478839 (NUMERAL 0)). Qed.
Lemma lem5478841 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5478842 : term132 = term325.
Proof. exact (MK_COMB (@lem5478841) (@lem5478840)). Qed.
Lemma lem5478843 : term324 = term326.
Proof. exact (MK_COMB (@lem5478842) (@lem5478837)). Qed.
Lemma lem5478844 : term327.
Proof. exact (@lem1980026 term130 term143 term175 term143). Qed.
Lemma lem5478846 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478847 : term265 = term271.
Proof. exact (@lem5478846 (NUMERAL 0) term144). Qed.
Lemma lem5478848 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478849 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478850 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478849 h1) (fun h1 : term271 = True => @lem5478848)). Qed.
Lemma lem5478851 : term271 = True.
Proof. exact (EQ_MP (@lem5478850) (@lem5478848)). Qed.
Lemma lem5478852 : term265 = True.
Proof. exact (TRANS (@lem5478847) (@lem5478851)). Qed.
Lemma lem5478853 : True = term265.
Proof. exact (SYM (@lem5478852)). Qed.
Lemma lem5478854 : term265.
Proof. exact (EQ_MP (@lem5478853) (@lem0)). Qed.
Lemma lem5478855 : term328.
Proof. exact (@lem5478844 (@lem5478854)). Qed.
Lemma lem5478857 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478858 : term265 = term271.
Proof. exact (@lem5478857 (NUMERAL 0) term144). Qed.
Lemma lem5478859 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478860 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478861 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478860 h1) (fun h1 : term271 = True => @lem5478859)). Qed.
Lemma lem5478862 : term271 = True.
Proof. exact (EQ_MP (@lem5478861) (@lem5478859)). Qed.
Lemma lem5478863 : term265 = True.
Proof. exact (TRANS (@lem5478858) (@lem5478862)). Qed.
Lemma lem5478864 : True = term265.
Proof. exact (SYM (@lem5478863)). Qed.
Lemma lem5478865 : term265.
Proof. exact (EQ_MP (@lem5478864) (@lem0)). Qed.
Lemma lem5478866 : term326 = term329.
Proof. exact (@lem5478855 (@lem5478865)). Qed.
Lemma lem5478868 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5478869 : term202 = term207.
Proof. exact (@lem5478868 term144 term144). Qed.
Lemma lem5478870 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478871 : term187 = term144.
Proof. exact (EQ_MP (@lem5478870) (@lem940073)). Qed.
Lemma lem5478872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478873 : term185 = term143.
Proof. exact (MK_COMB (@lem5478872) (@lem5478871)). Qed.
Lemma lem5478874 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5478875 : term207 = term175.
Proof. exact (MK_COMB (@lem5478874) (@lem5478873)). Qed.
Lemma lem5478876 : term202 = term175.
Proof. exact (TRANS (@lem5478869) (@lem5478875)). Qed.
Lemma lem5478878 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478879 : term276 = term130.
Proof. exact (@lem5478878 term144). Qed.
Lemma lem5478880 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5478881 : term330 = term132.
Proof. exact (MK_COMB (@lem5478880) (@lem5478879)). Qed.
Lemma lem5478882 : term329 = term324.
Proof. exact (MK_COMB (@lem5478881) (@lem5478876)). Qed.
Lemma lem5478884 (m : nat) (n : nat) : (term331 m n) = (term332 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5478885 : term324 = term333.
Proof. exact (@lem5478884 (NUMERAL 0) term144). Qed.
Lemma lem5478886 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478887 (h1 : term272 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5478888 : (term272 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478887 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5478886)). Qed.
Lemma lem5478889 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5478888) (@lem5478886)). Qed.
Lemma lem5478890 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5478891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5478892 : term334 = (and True).
Proof. exact (MK_COMB (@lem5478891) (@lem5478890)). Qed.
Lemma lem5478893 : term333 = (True /\ False).
Proof. exact (MK_COMB (@lem5478892) (@lem5478889)). Qed.
Lemma lem5478895 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5478896 : term333 = False.
Proof. exact (TRANS (@lem5478893) (@lem5478895)). Qed.
Lemma lem5478897 : term324 = False.
Proof. exact (TRANS (@lem5478885) (@lem5478896)). Qed.
Lemma lem5478898 : term329 = False.
Proof. exact (TRANS (@lem5478882) (@lem5478897)). Qed.
Lemma lem5478899 : term326 = False.
Proof. exact (TRANS (@lem5478866) (@lem5478898)). Qed.
Lemma lem5478900 : term324 = False.
Proof. exact (TRANS (@lem5478843) (@lem5478899)). Qed.
Lemma lem5478901 : term323 = False.
Proof. exact (TRANS (@lem5478834) (@lem5478900)). Qed.
Lemma lem5478902 (_70590 : int) (_70591 : int) (h1 : term335 _70590 _70591) : False.
Proof. exact (EQ_MP (@lem5478901) (@lem5478831 _70590 _70591 h1)). Qed.
Lemma lem5478903 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term352 _70590 _70591.
Proof. exact (h1). Qed.
Lemma lem5478904 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term260 _70590 _70591.
Proof. exact (proj2 (@lem5478903 _70590 _70591 h1)). Qed.
Lemma lem5478906 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term251 _70590 _70591.
Proof. exact (proj2 (@lem5478904 _70590 _70591 h1)). Qed.
Lemma lem5478908 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term217 _70590 _70591.
Proof. exact (proj2 (@lem5478906 _70590 _70591 h1)). Qed.
Lemma lem5478909 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term223 _70590 _70591.
Proof. exact (proj1 (@lem5478906 _70590 _70591 h1)). Qed.
Lemma lem5478911 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5478912 : term264 = term265.
Proof. exact (@lem5478911 term130 term143). Qed.
Lemma lem5478914 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478915 : term143 = term201.
Proof. exact (@lem5478914 term144). Qed.
Lemma lem5478917 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478918 : term130 = term172.
Proof. exact (@lem5478917 (NUMERAL 0)). Qed.
Lemma lem5478919 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478920 : term266 = term267.
Proof. exact (MK_COMB (@lem5478919) (@lem5478918)). Qed.
Lemma lem5478921 : term265 = term268.
Proof. exact (MK_COMB (@lem5478920) (@lem5478915)). Qed.
Lemma lem5478922 : term269.
Proof. exact (@lem1980255 term130 term143 term143 term143). Qed.
Lemma lem5478924 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478925 : term265 = term271.
Proof. exact (@lem5478924 (NUMERAL 0) term144). Qed.
Lemma lem5478926 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478927 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478928 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478927 h1) (fun h1 : term271 = True => @lem5478926)). Qed.
Lemma lem5478929 : term271 = True.
Proof. exact (EQ_MP (@lem5478928) (@lem5478926)). Qed.
Lemma lem5478930 : term265 = True.
Proof. exact (TRANS (@lem5478925) (@lem5478929)). Qed.
Lemma lem5478931 : True = term265.
Proof. exact (SYM (@lem5478930)). Qed.
Lemma lem5478932 : term265.
Proof. exact (EQ_MP (@lem5478931) (@lem0)). Qed.
Lemma lem5478933 : term273.
Proof. exact (@lem5478922 (@lem5478932)). Qed.
Lemma lem5478935 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478936 : term265 = term271.
Proof. exact (@lem5478935 (NUMERAL 0) term144). Qed.
Lemma lem5478937 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478938 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478939 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478938 h1) (fun h1 : term271 = True => @lem5478937)). Qed.
Lemma lem5478940 : term271 = True.
Proof. exact (EQ_MP (@lem5478939) (@lem5478937)). Qed.
Lemma lem5478941 : term265 = True.
Proof. exact (TRANS (@lem5478936) (@lem5478940)). Qed.
Lemma lem5478942 : True = term265.
Proof. exact (SYM (@lem5478941)). Qed.
Lemma lem5478943 : term265.
Proof. exact (EQ_MP (@lem5478942) (@lem0)). Qed.
Lemma lem5478944 : term268 = term274.
Proof. exact (@lem5478933 (@lem5478943)). Qed.
Lemma lem5478946 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5478947 : term184 = term185.
Proof. exact (@lem5478946 term144 term144). Qed.
Lemma lem5478948 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5478949 : term187 = term144.
Proof. exact (EQ_MP (@lem5478948) (@lem940073)). Qed.
Lemma lem5478950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5478951 : term185 = term143.
Proof. exact (MK_COMB (@lem5478950) (@lem5478949)). Qed.
Lemma lem5478952 : term184 = term143.
Proof. exact (TRANS (@lem5478947) (@lem5478951)). Qed.
Lemma lem5478954 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5478955 : term276 = term130.
Proof. exact (@lem5478954 term144). Qed.
Lemma lem5478956 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478957 : term277 = term266.
Proof. exact (MK_COMB (@lem5478956) (@lem5478955)). Qed.
Lemma lem5478958 : term274 = term265.
Proof. exact (MK_COMB (@lem5478957) (@lem5478952)). Qed.
Lemma lem5478960 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478961 : term265 = term271.
Proof. exact (@lem5478960 (NUMERAL 0) term144). Qed.
Lemma lem5478962 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5478963 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5478964 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5478963 h1) (fun h1 : term271 = True => @lem5478962)). Qed.
Lemma lem5478965 : term271 = True.
Proof. exact (EQ_MP (@lem5478964) (@lem5478962)). Qed.
Lemma lem5478966 : term265 = True.
Proof. exact (TRANS (@lem5478961) (@lem5478965)). Qed.
Lemma lem5478967 : term274 = True.
Proof. exact (TRANS (@lem5478958) (@lem5478966)). Qed.
Lemma lem5478968 : term268 = True.
Proof. exact (TRANS (@lem5478944) (@lem5478967)). Qed.
Lemma lem5478969 : term265 = True.
Proof. exact (TRANS (@lem5478921) (@lem5478968)). Qed.
Lemma lem5478970 : term264 = True.
Proof. exact (TRANS (@lem5478912) (@lem5478969)). Qed.
Lemma lem5478971 : True = term264.
Proof. exact (SYM (@lem5478970)). Qed.
Lemma lem5478972 : term264.
Proof. exact (EQ_MP (@lem5478971) (@lem0)). Qed.
Lemma lem5478973 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term278 _70590 _70591.
Proof. exact (conj (@lem5478972) (@lem5478909 _70590 _70591 h1)). Qed.
Lemma lem5478975 (x : real) (y : real) : term279 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5478976 (_70590 : int) (_70591 : int) : term280 _70590 _70591.
Proof. exact (@lem5478975 term143 (term220 _70590 _70591)). Qed.
Lemma lem5478977 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term281 _70590 _70591.
Proof. exact (@lem5478976 _70590 _70591 (@lem5478973 _70590 _70591 h1)). Qed.
Lemma lem5478978 (_70590 : int) (_70591 : int) : (term282 _70590 _70591) = (term220 _70590 _70591).
Proof. exact (@lem1982733 (term220 _70590 _70591)). Qed.
Lemma lem5478979 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5478980 (_70590 : int) (_70591 : int) : (term283 _70590 _70591) = (term222 _70590 _70591).
Proof. exact (MK_COMB (@lem5478979) (@lem5478978 _70590 _70591)). Qed.
Lemma lem5478981 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5478982 (_70590 : int) (_70591 : int) : (term281 _70590 _70591) = (term223 _70590 _70591).
Proof. exact (MK_COMB (@lem5478980 _70590 _70591) (@lem5478981)). Qed.
Lemma lem5478983 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term223 _70590 _70591.
Proof. exact (EQ_MP (@lem5478982 _70590 _70591) (@lem5478977 _70590 _70591 h1)). Qed.
Lemma lem5478985 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5478986 : term264 = term265.
Proof. exact (@lem5478985 term130 term143). Qed.
Lemma lem5478988 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478989 : term143 = term201.
Proof. exact (@lem5478988 term144). Qed.
Lemma lem5478991 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5478992 : term130 = term172.
Proof. exact (@lem5478991 (NUMERAL 0)). Qed.
Lemma lem5478993 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5478994 : term266 = term267.
Proof. exact (MK_COMB (@lem5478993) (@lem5478992)). Qed.
Lemma lem5478995 : term265 = term268.
Proof. exact (MK_COMB (@lem5478994) (@lem5478989)). Qed.
Lemma lem5478996 : term269.
Proof. exact (@lem1980255 term130 term143 term143 term143). Qed.
Lemma lem5478998 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5478999 : term265 = term271.
Proof. exact (@lem5478998 (NUMERAL 0) term144). Qed.
Lemma lem5479000 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479001 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479002 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479001 h1) (fun h1 : term271 = True => @lem5479000)). Qed.
Lemma lem5479003 : term271 = True.
Proof. exact (EQ_MP (@lem5479002) (@lem5479000)). Qed.
Lemma lem5479004 : term265 = True.
Proof. exact (TRANS (@lem5478999) (@lem5479003)). Qed.
Lemma lem5479005 : True = term265.
Proof. exact (SYM (@lem5479004)). Qed.
Lemma lem5479006 : term265.
Proof. exact (EQ_MP (@lem5479005) (@lem0)). Qed.
Lemma lem5479007 : term273.
Proof. exact (@lem5478996 (@lem5479006)). Qed.
Lemma lem5479009 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479010 : term265 = term271.
Proof. exact (@lem5479009 (NUMERAL 0) term144). Qed.
Lemma lem5479011 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479012 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479013 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479012 h1) (fun h1 : term271 = True => @lem5479011)). Qed.
Lemma lem5479014 : term271 = True.
Proof. exact (EQ_MP (@lem5479013) (@lem5479011)). Qed.
Lemma lem5479015 : term265 = True.
Proof. exact (TRANS (@lem5479010) (@lem5479014)). Qed.
Lemma lem5479016 : True = term265.
Proof. exact (SYM (@lem5479015)). Qed.
Lemma lem5479017 : term265.
Proof. exact (EQ_MP (@lem5479016) (@lem0)). Qed.
Lemma lem5479018 : term268 = term274.
Proof. exact (@lem5479007 (@lem5479017)). Qed.
Lemma lem5479020 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5479021 : term184 = term185.
Proof. exact (@lem5479020 term144 term144). Qed.
Lemma lem5479022 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479023 : term187 = term144.
Proof. exact (EQ_MP (@lem5479022) (@lem940073)). Qed.
Lemma lem5479024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479025 : term185 = term143.
Proof. exact (MK_COMB (@lem5479024) (@lem5479023)). Qed.
Lemma lem5479026 : term184 = term143.
Proof. exact (TRANS (@lem5479021) (@lem5479025)). Qed.
Lemma lem5479028 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5479029 : term276 = term130.
Proof. exact (@lem5479028 term144). Qed.
Lemma lem5479030 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5479031 : term277 = term266.
Proof. exact (MK_COMB (@lem5479030) (@lem5479029)). Qed.
Lemma lem5479032 : term274 = term265.
Proof. exact (MK_COMB (@lem5479031) (@lem5479026)). Qed.
Lemma lem5479034 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479035 : term265 = term271.
Proof. exact (@lem5479034 (NUMERAL 0) term144). Qed.
Lemma lem5479036 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479037 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479038 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479037 h1) (fun h1 : term271 = True => @lem5479036)). Qed.
Lemma lem5479039 : term271 = True.
Proof. exact (EQ_MP (@lem5479038) (@lem5479036)). Qed.
Lemma lem5479040 : term265 = True.
Proof. exact (TRANS (@lem5479035) (@lem5479039)). Qed.
Lemma lem5479041 : term274 = True.
Proof. exact (TRANS (@lem5479032) (@lem5479040)). Qed.
Lemma lem5479042 : term268 = True.
Proof. exact (TRANS (@lem5479018) (@lem5479041)). Qed.
Lemma lem5479043 : term265 = True.
Proof. exact (TRANS (@lem5478995) (@lem5479042)). Qed.
Lemma lem5479044 : term264 = True.
Proof. exact (TRANS (@lem5478986) (@lem5479043)). Qed.
Lemma lem5479045 : True = term264.
Proof. exact (SYM (@lem5479044)). Qed.
Lemma lem5479046 : term264.
Proof. exact (EQ_MP (@lem5479045) (@lem0)). Qed.
Lemma lem5479047 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term284 _70590 _70591.
Proof. exact (conj (@lem5479046) (@lem5478908 _70590 _70591 h1)). Qed.
Lemma lem5479049 (x : real) (y : real) : term279 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5479050 (_70590 : int) (_70591 : int) : term285 _70590 _70591.
Proof. exact (@lem5479049 term143 (term213 _70590 _70591)). Qed.
Lemma lem5479051 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term286 _70590 _70591.
Proof. exact (@lem5479050 _70590 _70591 (@lem5479047 _70590 _70591 h1)). Qed.
Lemma lem5479052 (_70590 : int) (_70591 : int) : (term287 _70590 _70591) = (term213 _70590 _70591).
Proof. exact (@lem1982733 (term213 _70590 _70591)). Qed.
Lemma lem5479053 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5479054 (_70590 : int) (_70591 : int) : (term288 _70590 _70591) = (term216 _70590 _70591).
Proof. exact (MK_COMB (@lem5479053) (@lem5479052 _70590 _70591)). Qed.
Lemma lem5479055 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5479056 (_70590 : int) (_70591 : int) : (term286 _70590 _70591) = (term217 _70590 _70591).
Proof. exact (MK_COMB (@lem5479054 _70590 _70591) (@lem5479055)). Qed.
Lemma lem5479057 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term217 _70590 _70591.
Proof. exact (EQ_MP (@lem5479056 _70590 _70591) (@lem5479051 _70590 _70591 h1)). Qed.
Lemma lem5479058 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term289 _70590 _70591.
Proof. exact (conj (@lem5479057 _70590 _70591 h1) (@lem5478983 _70590 _70591 h1)). Qed.
Lemma lem5479060 (x : real) (y : real) : term290 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5479061 (_70590 : int) (_70591 : int) : term291 _70590 _70591.
Proof. exact (@lem5479060 (term213 _70590 _70591) (term220 _70590 _70591)). Qed.
Lemma lem5479062 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term292 _70590 _70591.
Proof. exact (@lem5479061 _70590 _70591 (@lem5479058 _70590 _70591 h1)). Qed.
Lemma lem5479063 (_70590 : int) (_70591 : int) : (term293 _70590 _70591) = (term294 _70590 _70591).
Proof. exact (@lem1982753 (term214 _70590) (real_of_int _70590) (term295 _70591) (term214 _70591)). Qed.
Lemma lem5479064 (_70590 : int) : (term296 _70590) = (term297 _70590).
Proof. exact (@lem1982713 term175 (real_of_int _70590)). Qed.
Lemma lem5479066 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5479067 : term143 = term201.
Proof. exact (@lem5479066 term144). Qed.
Lemma lem5479069 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5479070 : term175 = term176.
Proof. exact (@lem5479069 term144). Qed.
Lemma lem5479071 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5479072 : term298 = term299.
Proof. exact (MK_COMB (@lem5479071) (@lem5479070)). Qed.
Lemma lem5479073 : term300 = term301.
Proof. exact (MK_COMB (@lem5479072) (@lem5479067)). Qed.
Lemma lem5479074 : term302.
Proof. exact (@lem1981473 term175 term143 term143 term143 term130 term143). Qed.
Lemma lem5479076 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479077 : term265 = term271.
Proof. exact (@lem5479076 (NUMERAL 0) term144). Qed.
Lemma lem5479078 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479079 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479080 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479079 h1) (fun h1 : term271 = True => @lem5479078)). Qed.
Lemma lem5479081 : term271 = True.
Proof. exact (EQ_MP (@lem5479080) (@lem5479078)). Qed.
Lemma lem5479082 : term265 = True.
Proof. exact (TRANS (@lem5479077) (@lem5479081)). Qed.
Lemma lem5479083 : True = term265.
Proof. exact (SYM (@lem5479082)). Qed.
Lemma lem5479084 : term265.
Proof. exact (EQ_MP (@lem5479083) (@lem0)). Qed.
Lemma lem5479085 : term303.
Proof. exact (@lem5479074 (@lem5479084)). Qed.
Lemma lem5479087 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479088 : term265 = term271.
Proof. exact (@lem5479087 (NUMERAL 0) term144). Qed.
Lemma lem5479089 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479090 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479091 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479090 h1) (fun h1 : term271 = True => @lem5479089)). Qed.
Lemma lem5479092 : term271 = True.
Proof. exact (EQ_MP (@lem5479091) (@lem5479089)). Qed.
Lemma lem5479093 : term265 = True.
Proof. exact (TRANS (@lem5479088) (@lem5479092)). Qed.
Lemma lem5479094 : True = term265.
Proof. exact (SYM (@lem5479093)). Qed.
Lemma lem5479095 : term265.
Proof. exact (EQ_MP (@lem5479094) (@lem0)). Qed.
Lemma lem5479096 : term304.
Proof. exact (@lem5479085 (@lem5479095)). Qed.
Lemma lem5479098 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479099 : term265 = term271.
Proof. exact (@lem5479098 (NUMERAL 0) term144). Qed.
Lemma lem5479100 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479101 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479102 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479101 h1) (fun h1 : term271 = True => @lem5479100)). Qed.
Lemma lem5479103 : term271 = True.
Proof. exact (EQ_MP (@lem5479102) (@lem5479100)). Qed.
Lemma lem5479104 : term265 = True.
Proof. exact (TRANS (@lem5479099) (@lem5479103)). Qed.
Lemma lem5479105 : True = term265.
Proof. exact (SYM (@lem5479104)). Qed.
Lemma lem5479106 : term265.
Proof. exact (EQ_MP (@lem5479105) (@lem0)). Qed.
Lemma lem5479107 : term305.
Proof. exact (@lem5479096 (@lem5479106)). Qed.
Lemma lem5479109 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5479110 : term184 = term185.
Proof. exact (@lem5479109 term144 term144). Qed.
Lemma lem5479111 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479112 : term187 = term144.
Proof. exact (EQ_MP (@lem5479111) (@lem940073)). Qed.
Lemma lem5479113 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479114 : term185 = term143.
Proof. exact (MK_COMB (@lem5479113) (@lem5479112)). Qed.
Lemma lem5479115 : term184 = term143.
Proof. exact (TRANS (@lem5479110) (@lem5479114)). Qed.
Lemma lem5479117 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5479118 : term202 = term207.
Proof. exact (@lem5479117 term144 term144). Qed.
Lemma lem5479119 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479120 : term187 = term144.
Proof. exact (EQ_MP (@lem5479119) (@lem940073)). Qed.
Lemma lem5479121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479122 : term185 = term143.
Proof. exact (MK_COMB (@lem5479121) (@lem5479120)). Qed.
Lemma lem5479123 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5479124 : term207 = term175.
Proof. exact (MK_COMB (@lem5479123) (@lem5479122)). Qed.
Lemma lem5479125 : term202 = term175.
Proof. exact (TRANS (@lem5479118) (@lem5479124)). Qed.
Lemma lem5479126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5479127 : term306 = term298.
Proof. exact (MK_COMB (@lem5479126) (@lem5479125)). Qed.
Lemma lem5479128 : term307 = term300.
Proof. exact (MK_COMB (@lem5479127) (@lem5479115)). Qed.
Lemma lem5479130 (m : nat) : (term308 m) = term130.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5479131 : term300 = term130.
Proof. exact (@lem5479130 term144). Qed.
Lemma lem5479132 : term307 = term130.
Proof. exact (TRANS (@lem5479128) (@lem5479131)). Qed.
Lemma lem5479133 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5479134 : term309 = term310.
Proof. exact (MK_COMB (@lem5479133) (@lem5479132)). Qed.
Lemma lem5479135 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5479136 : term311 = term276.
Proof. exact (MK_COMB (@lem5479134) (@lem5479135)). Qed.
Lemma lem5479138 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5479139 : term276 = term130.
Proof. exact (@lem5479138 term144). Qed.
Lemma lem5479140 : term311 = term130.
Proof. exact (TRANS (@lem5479136) (@lem5479139)). Qed.
Lemma lem5479142 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5479143 : term184 = term185.
Proof. exact (@lem5479142 term144 term144). Qed.
Lemma lem5479144 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479145 : term187 = term144.
Proof. exact (EQ_MP (@lem5479144) (@lem940073)). Qed.
Lemma lem5479146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479147 : term185 = term143.
Proof. exact (MK_COMB (@lem5479146) (@lem5479145)). Qed.
Lemma lem5479148 : term184 = term143.
Proof. exact (TRANS (@lem5479143) (@lem5479147)). Qed.
Lemma lem5479149 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem5479150 : term312 = term276.
Proof. exact (MK_COMB (@lem5479149) (@lem5479148)). Qed.
Lemma lem5479152 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5479153 : term276 = term130.
Proof. exact (@lem5479152 term144). Qed.
Lemma lem5479154 : term312 = term130.
Proof. exact (TRANS (@lem5479150) (@lem5479153)). Qed.
Lemma lem5479155 : term130 = term312.
Proof. exact (SYM (@lem5479154)). Qed.
Lemma lem5479156 : term311 = term312.
Proof. exact (TRANS (@lem5479140) (@lem5479155)). Qed.
Lemma lem5479157 : term301 = term172.
Proof. exact (@lem5479107 (@lem5479156)). Qed.
Lemma lem5479158 : term300 = term172.
Proof. exact (TRANS (@lem5479073) (@lem5479157)). Qed.
Lemma lem5479160 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5479161 : term172 = term130.
Proof. exact (@lem5479160 term130). Qed.
Lemma lem5479162 : term300 = term130.
Proof. exact (TRANS (@lem5479158) (@lem5479161)). Qed.
Lemma lem5479163 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5479164 : term313 = term310.
Proof. exact (MK_COMB (@lem5479163) (@lem5479162)). Qed.
Lemma lem5479165 (_70590 : int) : (real_of_int _70590) = (real_of_int _70590).
Proof. exact (eq_refl (real_of_int _70590)). Qed.
Lemma lem5479166 (_70590 : int) : (term297 _70590) = (term314 _70590).
Proof. exact (MK_COMB (@lem5479164) (@lem5479165 _70590)). Qed.
Lemma lem5479167 (_70590 : int) : (term296 _70590) = (term314 _70590).
Proof. exact (TRANS (@lem5479064 _70590) (@lem5479166 _70590)). Qed.
Lemma lem5479168 (_70590 : int) : (term314 _70590) = term130.
Proof. exact (@lem1982719 (real_of_int _70590)). Qed.
Lemma lem5479169 (_70590 : int) : (term296 _70590) = term130.
Proof. exact (TRANS (@lem5479167 _70590) (@lem5479168 _70590)). Qed.
Lemma lem5479170 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5479171 (_70590 : int) : (term315 _70590) = term231.
Proof. exact (MK_COMB (@lem5479170) (@lem5479169 _70590)). Qed.
Lemma lem5479172 (_70591 : int) : (term316 _70591) = (term317 _70591).
Proof. exact (@lem1982759 (real_of_int _70591) (term214 _70591) term175). Qed.
Lemma lem5479173 (_70591 : int) : (term318 _70591) = (term297 _70591).
Proof. exact (@lem1982715 term175 (real_of_int _70591)). Qed.
Lemma lem5479175 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5479176 : term143 = term201.
Proof. exact (@lem5479175 term144). Qed.
Lemma lem5479178 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5479179 : term175 = term176.
Proof. exact (@lem5479178 term144). Qed.
Lemma lem5479180 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5479181 : term298 = term299.
Proof. exact (MK_COMB (@lem5479180) (@lem5479179)). Qed.
Lemma lem5479182 : term300 = term301.
Proof. exact (MK_COMB (@lem5479181) (@lem5479176)). Qed.
Lemma lem5479183 : term302.
Proof. exact (@lem1981473 term175 term143 term143 term143 term130 term143). Qed.
Lemma lem5479185 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479186 : term265 = term271.
Proof. exact (@lem5479185 (NUMERAL 0) term144). Qed.
Lemma lem5479187 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479188 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479189 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479188 h1) (fun h1 : term271 = True => @lem5479187)). Qed.
Lemma lem5479190 : term271 = True.
Proof. exact (EQ_MP (@lem5479189) (@lem5479187)). Qed.
Lemma lem5479191 : term265 = True.
Proof. exact (TRANS (@lem5479186) (@lem5479190)). Qed.
Lemma lem5479192 : True = term265.
Proof. exact (SYM (@lem5479191)). Qed.
Lemma lem5479193 : term265.
Proof. exact (EQ_MP (@lem5479192) (@lem0)). Qed.
Lemma lem5479194 : term303.
Proof. exact (@lem5479183 (@lem5479193)). Qed.
Lemma lem5479196 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479197 : term265 = term271.
Proof. exact (@lem5479196 (NUMERAL 0) term144). Qed.
Lemma lem5479198 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479199 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479200 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479199 h1) (fun h1 : term271 = True => @lem5479198)). Qed.
Lemma lem5479201 : term271 = True.
Proof. exact (EQ_MP (@lem5479200) (@lem5479198)). Qed.
Lemma lem5479202 : term265 = True.
Proof. exact (TRANS (@lem5479197) (@lem5479201)). Qed.
Lemma lem5479203 : True = term265.
Proof. exact (SYM (@lem5479202)). Qed.
Lemma lem5479204 : term265.
Proof. exact (EQ_MP (@lem5479203) (@lem0)). Qed.
Lemma lem5479205 : term304.
Proof. exact (@lem5479194 (@lem5479204)). Qed.
Lemma lem5479207 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479208 : term265 = term271.
Proof. exact (@lem5479207 (NUMERAL 0) term144). Qed.
Lemma lem5479209 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479210 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479211 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479210 h1) (fun h1 : term271 = True => @lem5479209)). Qed.
Lemma lem5479212 : term271 = True.
Proof. exact (EQ_MP (@lem5479211) (@lem5479209)). Qed.
Lemma lem5479213 : term265 = True.
Proof. exact (TRANS (@lem5479208) (@lem5479212)). Qed.
Lemma lem5479214 : True = term265.
Proof. exact (SYM (@lem5479213)). Qed.
Lemma lem5479215 : term265.
Proof. exact (EQ_MP (@lem5479214) (@lem0)). Qed.
Lemma lem5479216 : term305.
Proof. exact (@lem5479205 (@lem5479215)). Qed.
Lemma lem5479218 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5479219 : term184 = term185.
Proof. exact (@lem5479218 term144 term144). Qed.
Lemma lem5479220 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479221 : term187 = term144.
Proof. exact (EQ_MP (@lem5479220) (@lem940073)). Qed.
Lemma lem5479222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479223 : term185 = term143.
Proof. exact (MK_COMB (@lem5479222) (@lem5479221)). Qed.
Lemma lem5479224 : term184 = term143.
Proof. exact (TRANS (@lem5479219) (@lem5479223)). Qed.
Lemma lem5479226 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5479227 : term202 = term207.
Proof. exact (@lem5479226 term144 term144). Qed.
Lemma lem5479228 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479229 : term187 = term144.
Proof. exact (EQ_MP (@lem5479228) (@lem940073)). Qed.
Lemma lem5479230 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479231 : term185 = term143.
Proof. exact (MK_COMB (@lem5479230) (@lem5479229)). Qed.
Lemma lem5479232 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5479233 : term207 = term175.
Proof. exact (MK_COMB (@lem5479232) (@lem5479231)). Qed.
Lemma lem5479234 : term202 = term175.
Proof. exact (TRANS (@lem5479227) (@lem5479233)). Qed.
Lemma lem5479235 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5479236 : term306 = term298.
Proof. exact (MK_COMB (@lem5479235) (@lem5479234)). Qed.
Lemma lem5479237 : term307 = term300.
Proof. exact (MK_COMB (@lem5479236) (@lem5479224)). Qed.
Lemma lem5479239 (m : nat) : (term308 m) = term130.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5479240 : term300 = term130.
Proof. exact (@lem5479239 term144). Qed.
Lemma lem5479241 : term307 = term130.
Proof. exact (TRANS (@lem5479237) (@lem5479240)). Qed.
Lemma lem5479242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5479243 : term309 = term310.
Proof. exact (MK_COMB (@lem5479242) (@lem5479241)). Qed.
Lemma lem5479244 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem5479245 : term311 = term276.
Proof. exact (MK_COMB (@lem5479243) (@lem5479244)). Qed.
Lemma lem5479247 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5479248 : term276 = term130.
Proof. exact (@lem5479247 term144). Qed.
Lemma lem5479249 : term311 = term130.
Proof. exact (TRANS (@lem5479245) (@lem5479248)). Qed.
Lemma lem5479251 (m : nat) (n : nat) : (term182 m n) = (term183 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5479252 : term184 = term185.
Proof. exact (@lem5479251 term144 term144). Qed.
Lemma lem5479253 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479254 : term187 = term144.
Proof. exact (EQ_MP (@lem5479253) (@lem940073)). Qed.
Lemma lem5479255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479256 : term185 = term143.
Proof. exact (MK_COMB (@lem5479255) (@lem5479254)). Qed.
Lemma lem5479257 : term184 = term143.
Proof. exact (TRANS (@lem5479252) (@lem5479256)). Qed.
Lemma lem5479258 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem5479259 : term312 = term276.
Proof. exact (MK_COMB (@lem5479258) (@lem5479257)). Qed.
Lemma lem5479261 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5479262 : term276 = term130.
Proof. exact (@lem5479261 term144). Qed.
Lemma lem5479263 : term312 = term130.
Proof. exact (TRANS (@lem5479259) (@lem5479262)). Qed.
Lemma lem5479264 : term130 = term312.
Proof. exact (SYM (@lem5479263)). Qed.
Lemma lem5479265 : term311 = term312.
Proof. exact (TRANS (@lem5479249) (@lem5479264)). Qed.
Lemma lem5479266 : term301 = term172.
Proof. exact (@lem5479216 (@lem5479265)). Qed.
Lemma lem5479267 : term300 = term172.
Proof. exact (TRANS (@lem5479182) (@lem5479266)). Qed.
Lemma lem5479269 (x : real) : (term191 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5479270 : term172 = term130.
Proof. exact (@lem5479269 term130). Qed.
Lemma lem5479271 : term300 = term130.
Proof. exact (TRANS (@lem5479267) (@lem5479270)). Qed.
Lemma lem5479272 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5479273 : term313 = term310.
Proof. exact (MK_COMB (@lem5479272) (@lem5479271)). Qed.
Lemma lem5479274 (_70591 : int) : (real_of_int _70591) = (real_of_int _70591).
Proof. exact (eq_refl (real_of_int _70591)). Qed.
Lemma lem5479275 (_70591 : int) : (term297 _70591) = (term314 _70591).
Proof. exact (MK_COMB (@lem5479273) (@lem5479274 _70591)). Qed.
Lemma lem5479276 (_70591 : int) : (term318 _70591) = (term314 _70591).
Proof. exact (TRANS (@lem5479173 _70591) (@lem5479275 _70591)). Qed.
Lemma lem5479277 (_70591 : int) : (term314 _70591) = term130.
Proof. exact (@lem1982719 (real_of_int _70591)). Qed.
Lemma lem5479278 (_70591 : int) : (term318 _70591) = term130.
Proof. exact (TRANS (@lem5479276 _70591) (@lem5479277 _70591)). Qed.
Lemma lem5479279 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5479280 (_70591 : int) : (term319 _70591) = term231.
Proof. exact (MK_COMB (@lem5479279) (@lem5479278 _70591)). Qed.
Lemma lem5479281 : term175 = term175.
Proof. exact (eq_refl term175). Qed.
Lemma lem5479282 (_70591 : int) : (term317 _70591) = term320.
Proof. exact (MK_COMB (@lem5479280 _70591) (@lem5479281)). Qed.
Lemma lem5479283 (_70591 : int) : (term316 _70591) = term320.
Proof. exact (TRANS (@lem5479172 _70591) (@lem5479282 _70591)). Qed.
Lemma lem5479284 : term320 = term175.
Proof. exact (@lem1982721 term175). Qed.
Lemma lem5479285 (_70591 : int) : (term316 _70591) = term175.
Proof. exact (TRANS (@lem5479283 _70591) (@lem5479284)). Qed.
Lemma lem5479286 (_70590 : int) (_70591 : int) : (term294 _70590 _70591) = term320.
Proof. exact (MK_COMB (@lem5479171 _70590) (@lem5479285 _70591)). Qed.
Lemma lem5479287 (_70590 : int) (_70591 : int) : (term293 _70590 _70591) = term320.
Proof. exact (TRANS (@lem5479063 _70590 _70591) (@lem5479286 _70590 _70591)). Qed.
Lemma lem5479288 : term320 = term175.
Proof. exact (@lem1982721 term175). Qed.
Lemma lem5479289 (_70590 : int) (_70591 : int) : (term293 _70590 _70591) = term175.
Proof. exact (TRANS (@lem5479287 _70590 _70591) (@lem5479288)). Qed.
Lemma lem5479290 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5479291 (_70590 : int) (_70591 : int) : (term321 _70590 _70591) = term322.
Proof. exact (MK_COMB (@lem5479290) (@lem5479289 _70590 _70591)). Qed.
Lemma lem5479292 : term130 = term130.
Proof. exact (eq_refl term130). Qed.
Lemma lem5479293 (_70590 : int) (_70591 : int) : (term292 _70590 _70591) = term323.
Proof. exact (MK_COMB (@lem5479291 _70590 _70591) (@lem5479292)). Qed.
Lemma lem5479294 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : term323.
Proof. exact (EQ_MP (@lem5479293 _70590 _70591) (@lem5479062 _70590 _70591 h1)). Qed.
Lemma lem5479296 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5479297 : term323 = term324.
Proof. exact (@lem5479296 term130 term175). Qed.
Lemma lem5479299 (x : nat) : (term173 x) = (term174 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5479300 : term175 = term176.
Proof. exact (@lem5479299 term144). Qed.
Lemma lem5479302 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5479303 : term130 = term172.
Proof. exact (@lem5479302 (NUMERAL 0)). Qed.
Lemma lem5479304 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5479305 : term132 = term325.
Proof. exact (MK_COMB (@lem5479304) (@lem5479303)). Qed.
Lemma lem5479306 : term324 = term326.
Proof. exact (MK_COMB (@lem5479305) (@lem5479300)). Qed.
Lemma lem5479307 : term327.
Proof. exact (@lem1980026 term130 term143 term175 term143). Qed.
Lemma lem5479309 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479310 : term265 = term271.
Proof. exact (@lem5479309 (NUMERAL 0) term144). Qed.
Lemma lem5479311 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479312 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479313 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479312 h1) (fun h1 : term271 = True => @lem5479311)). Qed.
Lemma lem5479314 : term271 = True.
Proof. exact (EQ_MP (@lem5479313) (@lem5479311)). Qed.
Lemma lem5479315 : term265 = True.
Proof. exact (TRANS (@lem5479310) (@lem5479314)). Qed.
Lemma lem5479316 : True = term265.
Proof. exact (SYM (@lem5479315)). Qed.
Lemma lem5479317 : term265.
Proof. exact (EQ_MP (@lem5479316) (@lem0)). Qed.
Lemma lem5479318 : term328.
Proof. exact (@lem5479307 (@lem5479317)). Qed.
Lemma lem5479320 (m : nat) (n : nat) : (term270 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5479321 : term265 = term271.
Proof. exact (@lem5479320 (NUMERAL 0) term144). Qed.
Lemma lem5479322 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479323 (h1 : term272 = (BIT1 0)) : term271 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5479324 : (term272 = (BIT1 0)) = (term271 = True).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479323 h1) (fun h1 : term271 = True => @lem5479322)). Qed.
Lemma lem5479325 : term271 = True.
Proof. exact (EQ_MP (@lem5479324) (@lem5479322)). Qed.
Lemma lem5479326 : term265 = True.
Proof. exact (TRANS (@lem5479321) (@lem5479325)). Qed.
Lemma lem5479327 : True = term265.
Proof. exact (SYM (@lem5479326)). Qed.
Lemma lem5479328 : term265.
Proof. exact (EQ_MP (@lem5479327) (@lem0)). Qed.
Lemma lem5479329 : term326 = term329.
Proof. exact (@lem5479318 (@lem5479328)). Qed.
Lemma lem5479331 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5479332 : term202 = term207.
Proof. exact (@lem5479331 term144 term144). Qed.
Lemma lem5479333 : (term186 = (BIT1 0)) = (term187 = term144).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5479334 : term187 = term144.
Proof. exact (EQ_MP (@lem5479333) (@lem940073)). Qed.
Lemma lem5479335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5479336 : term185 = term143.
Proof. exact (MK_COMB (@lem5479335) (@lem5479334)). Qed.
Lemma lem5479337 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5479338 : term207 = term175.
Proof. exact (MK_COMB (@lem5479337) (@lem5479336)). Qed.
Lemma lem5479339 : term202 = term175.
Proof. exact (TRANS (@lem5479332) (@lem5479338)). Qed.
Lemma lem5479341 (x : nat) : (term275 x) = term130.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5479342 : term276 = term130.
Proof. exact (@lem5479341 term144). Qed.
Lemma lem5479343 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5479344 : term330 = term132.
Proof. exact (MK_COMB (@lem5479343) (@lem5479342)). Qed.
Lemma lem5479345 : term329 = term324.
Proof. exact (MK_COMB (@lem5479344) (@lem5479339)). Qed.
Lemma lem5479347 (m : nat) (n : nat) : (term331 m n) = (term332 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5479348 : term324 = term333.
Proof. exact (@lem5479347 (NUMERAL 0) term144). Qed.
Lemma lem5479349 : term272 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5479350 (h1 : term272 = (BIT1 0)) : (term144 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5479351 : (term272 = (BIT1 0)) = ((term144 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term272 = (BIT1 0) => @lem5479350 h1) (fun h1 : (term144 = (NUMERAL 0)) = False => @lem5479349)). Qed.
Lemma lem5479352 : (term144 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5479351) (@lem5479349)). Qed.
Lemma lem5479353 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5479354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5479355 : term334 = (and True).
Proof. exact (MK_COMB (@lem5479354) (@lem5479353)). Qed.
Lemma lem5479356 : term333 = (True /\ False).
Proof. exact (MK_COMB (@lem5479355) (@lem5479352)). Qed.
Lemma lem5479358 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5479359 : term333 = False.
Proof. exact (TRANS (@lem5479356) (@lem5479358)). Qed.
Lemma lem5479360 : term324 = False.
Proof. exact (TRANS (@lem5479348) (@lem5479359)). Qed.
Lemma lem5479361 : term329 = False.
Proof. exact (TRANS (@lem5479345) (@lem5479360)). Qed.
Lemma lem5479362 : term326 = False.
Proof. exact (TRANS (@lem5479329) (@lem5479361)). Qed.
Lemma lem5479363 : term324 = False.
Proof. exact (TRANS (@lem5479306) (@lem5479362)). Qed.
Lemma lem5479364 : term323 = False.
Proof. exact (TRANS (@lem5479297) (@lem5479363)). Qed.
Lemma lem5479365 (_70590 : int) (_70591 : int) (h1 : term352 _70590 _70591) : False.
Proof. exact (EQ_MP (@lem5479364) (@lem5479294 _70590 _70591 h1)). Qed.
Lemma lem5479366 (_70590 : int) (_70591 : int) (h1 : term258 _70590 _70591) : False.
Proof. exact (or_elim (@lem5478552 _70590 _70591 h1) (fun h0 : term335 _70590 _70591 => @lem5478902 _70590 _70591 h0) (fun h0 : term352 _70590 _70591 => @lem5479365 _70590 _70591 h0)). Qed.
Lemma lem5479367 (_70590 : int) (_70591 : int) (h1 : term262 _70590 _70591) : False.
Proof. exact (or_elim (@lem5478086 _70590 _70591 h1) (fun h0 : term263 _70590 _70591 => @lem5478551 _70590 _70591 h0) (fun h0 : term258 _70590 _70591 => @lem5479366 _70590 _70591 h0)). Qed.
Lemma lem5479369 (_70590 : int) (_70591 : int) (h1 : term262 _70590 _70591) : term262 _70590 _70591.
Proof. exact (h1). Qed.
Lemma lem5479370 (_70590 : int) (_70591 : int) (h1 : term262 _70590 _70591) : (term262 _70590 _70591) = False.
Proof. exact (prop_ext (fun h2 : term262 _70590 _70591 => @lem5479367 _70590 _70591 h1) (fun h2 : False => @lem5479369 _70590 _70591 h1)). Qed.
Lemma lem5479371 (_70590 : int) (_70591 : int) (h1 : term262 _70590 _70591) : False.
Proof. exact (EQ_MP (@lem5479370 _70590 _70591 h1) (@lem5479369 _70590 _70591 h1)). Qed.
Lemma lem5479372 (_70590 : int) (_70591 : int) (h1 : term167 _70590 _70591) : term167 _70590 _70591.
Proof. exact (h1). Qed.
Lemma lem5479373 (_70590 : int) (_70591 : int) (h1 : term167 _70590 _70591) : term262 _70590 _70591.
Proof. exact (EQ_MP (@lem5478070 _70590 _70591) (@lem5479372 _70590 _70591 h1)). Qed.
Lemma lem5479374 (_70590 : int) (_70591 : int) (h1 : term167 _70590 _70591) : (term262 _70590 _70591) = False.
Proof. exact (prop_ext (fun h2 : term262 _70590 _70591 => @lem5479371 _70590 _70591 h2) (fun h2 : False => @lem5479373 _70590 _70591 h1)). Qed.
Lemma lem5479375 (_70590 : int) (_70591 : int) (h1 : term167 _70590 _70591) : False.
Proof. exact (EQ_MP (@lem5479374 _70590 _70591 h1) (@lem5479373 _70590 _70591 h1)). Qed.
Lemma lem5479376 (_70590 : int) (_70591 : int) : term353 _70590 _70591.
Proof. exact (fun h0 : term167 _70590 _70591 => @lem5479375 _70590 _70591 h0). Qed.
Lemma lem5479377 (_70590 : int) (_70591 : int) : term354 _70590 _70591.
Proof. exact (@lem1386578 (term355 _70590 _70591)). Qed.
Lemma lem5479380 (_70590 : int) (_70591 : int) : term355 _70590 _70591.
Proof. exact (@lem5479377 _70590 _70591 (@lem5479376 _70590 _70591)). Qed.
Lemma lem5479381 (_70591 : int) (_70590 : int) : (term165 _70590 _70591) = (term123 _70591 _70590).
Proof. exact (SYM (@lem5477501 _70590 _70591)). Qed.
Lemma lem5479382 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5479383 (_70591 : int) (_70590 : int) : (term355 _70590 _70591) = (term87 _70591 _70590).
Proof. exact (MK_COMB (@lem5479382) (@lem5479381 _70591 _70590)). Qed.
Lemma lem5479384 (_70591 : int) (_70590 : int) : term87 _70591 _70590.
Proof. exact (EQ_MP (@lem5479383 _70591 _70590) (@lem5479380 _70590 _70591)). Qed.
Lemma lem5479385 (_70591 : int) (_70590 : int) : term88 _70591 _70590.
Proof. exact (EQ_MP (@lem5477260 _70591 _70590) (@lem5479384 _70591 _70590)). Qed.
Lemma lem5479386 (x : nat) (n : nat) : term356 x n.
Proof. exact (@lem5479385 (int_of_num x) (int_of_num n)). Qed.
Lemma lem5479387 (x : nat) (n : nat) : term357 x n.
Proof. exact (@lem5479386 x n (@lem5477256 n)). Qed.
Lemma lem5479388 (x : nat) (n : nat) : term81 x n.
Proof. exact (@lem5479387 x n (@lem5477259 x)). Qed.
Lemma lem5479389 (n : nat) : term83 n.
Proof. exact (fun x : nat => @lem5479388 x n). Qed.
Lemma lem5479390 : term85.
Proof. exact (fun n : nat => @lem5479389 n). Qed.
Lemma lem5479391 : term85 = term47.
Proof. exact (SYM (@lem5477253)). Qed.
Lemma lem5479392 : term47.
Proof. exact (EQ_MP (@lem5479391) (@lem5479390)). Qed.
Lemma lem5479393 : term47 = (term47 = True).
Proof. exact (@lem7 term47). Qed.
Lemma lem5479394 : term47 = True.
Proof. exact (EQ_MP (@lem5479393) (@lem5479392)). Qed.
Lemma lem5479395 : True = term47.
Proof. exact (SYM (@lem5479394)). Qed.
Lemma lem5479396 : term47.
Proof. exact (EQ_MP (@lem5479395) (@lem0)). Qed.
Lemma lem5479397 : term46.
Proof. exact (EQ_MP (@lem5477054) (@lem5479396)). Qed.
