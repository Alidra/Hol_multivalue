Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2339318_term_abbrevs.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2338243_spec.
Require Import thm2338244_spec.
Require Import thm2338249_spec.
Require Import thm2338250_spec.
Require Import thm2338252_spec.
Require Import thm2338253_spec.
Require Import thm2338255_spec.
Require Import thm2338256_spec.
Require Import thm2338271_spec.
Require Import thm2338272_spec.
Require Import thm2338274_spec.
Require Import thm2338275_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem2338997 (P : int -> Prop) : (term0 P) = (term1 P).
Proof. exact (EQ_MP (@lem2338275 P) (@lem2338274 P)). Qed.
Lemma lem2338998 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem2338997 (term4 P)). Qed.
Lemma lem2338999 (P : int -> Prop) (x : int) : (term5 P x) = (term6 P x).
Proof. exact (eq_refl (term5 P x)). Qed.
Lemma lem2339000 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2339001 (P : int -> Prop) (x : int) : (term8 P x) = (term9 P x).
Proof. exact (MK_COMB (@lem2339000 x) (@lem2338999 P x)). Qed.
Lemma lem2339002 (P : int -> Prop) : (term10 P) = (term11 P).
Proof. exact (fun_ext (fun x : int => @lem2339001 P x)). Qed.
Lemma lem2339003 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2339004 (P : int -> Prop) : (term2 P) = (term12 P).
Proof. exact (MK_COMB (@lem2339003) (@lem2339002 P)). Qed.
Lemma lem2339005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339006 (P : int -> Prop) : (term13 P) = (term14 P).
Proof. exact (MK_COMB (@lem2339005) (@lem2339004 P)). Qed.
Lemma lem2339007 (P : int -> Prop) (n : nat) : (term15 P n) = (term16 P n).
Proof. exact (eq_refl (term15 P n)). Qed.
Lemma lem2339008 (P : int -> Prop) : (term17 P) = (term18 P).
Proof. exact (fun_ext (fun n : nat => @lem2339007 P n)). Qed.
Lemma lem2339009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339010 (P : int -> Prop) : (term3 P) = (term19 P).
Proof. exact (MK_COMB (@lem2339009) (@lem2339008 P)). Qed.
Lemma lem2339011 (P : int -> Prop) : ((term2 P) = (term3 P)) = ((term12 P) = (term19 P)).
Proof. exact (MK_COMB (@lem2339006 P) (@lem2339010 P)). Qed.
Lemma lem2339012 (P : int -> Prop) : (term12 P) = (term19 P).
Proof. exact (EQ_MP (@lem2339011 P) (@lem2338998 P)). Qed.
Lemma lem2339017 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2339018 (P : int -> Prop) : (term20 P) = (term21 P).
Proof. exact (MK_COMB (@lem2339017) (@lem2339012 P)). Qed.
Lemma lem2339019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339020 (P : int -> Prop) : (term22 P) = (term23 P).
Proof. exact (MK_COMB (@lem2339019) (@lem2339018 P)). Qed.
Lemma lem2339022 (P : int -> Prop) : (term0 P) = (term1 P).
Proof. exact (EQ_MP (@lem2338275 P) (@lem2338274 P)). Qed.
Lemma lem2339023 (P : int -> Prop) : (term24 P) = (term25 P).
Proof. exact (@lem2339022 (term26 P)). Qed.
Lemma lem2339024 (P : int -> Prop) (x : int) : (term27 P x) = (term28 P x).
Proof. exact (eq_refl (term27 P x)). Qed.
Lemma lem2339025 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2339026 (P : int -> Prop) (x : int) : (term29 P x) = (term30 P x).
Proof. exact (MK_COMB (@lem2339025 x) (@lem2339024 P x)). Qed.
Lemma lem2339027 (P : int -> Prop) : (term31 P) = (term32 P).
Proof. exact (fun_ext (fun x : int => @lem2339026 P x)). Qed.
Lemma lem2339028 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2339029 (P : int -> Prop) : (term24 P) = (term33 P).
Proof. exact (MK_COMB (@lem2339028) (@lem2339027 P)). Qed.
Lemma lem2339030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339031 (P : int -> Prop) : (term34 P) = (term35 P).
Proof. exact (MK_COMB (@lem2339030) (@lem2339029 P)). Qed.
Lemma lem2339032 (P : int -> Prop) (n : nat) : (term36 P n) = (term37 P n).
Proof. exact (eq_refl (term36 P n)). Qed.
Lemma lem2339033 (P : int -> Prop) : (term38 P) = (term39 P).
Proof. exact (fun_ext (fun n : nat => @lem2339032 P n)). Qed.
Lemma lem2339034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339035 (P : int -> Prop) : (term25 P) = (term40 P).
Proof. exact (MK_COMB (@lem2339034) (@lem2339033 P)). Qed.
Lemma lem2339036 (P : int -> Prop) : ((term24 P) = (term25 P)) = ((term33 P) = (term40 P)).
Proof. exact (MK_COMB (@lem2339031 P) (@lem2339035 P)). Qed.
Lemma lem2339037 (P : int -> Prop) : (term33 P) = (term40 P).
Proof. exact (EQ_MP (@lem2339036 P) (@lem2339023 P)). Qed.
Lemma lem2339049 (p : Prop) (q : Prop) (r : Prop) : (term41 p q r) = (term42 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem2339050 (P : int -> Prop) (n : nat) (y : int) : (term43 P n y) = (term44 P n y).
Proof. exact (@lem2339049 (term45 y) (P y) (term46 n y)). Qed.
Lemma lem2339055 (P : int -> Prop) (n : nat) : (term47 P n) = (term48 P n).
Proof. exact (fun_ext (fun y : int => @lem2339050 P n y)). Qed.
Lemma lem2339056 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2339057 (P : int -> Prop) (n : nat) : (term49 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem2339056) (@lem2339055 P n)). Qed.
Lemma lem2339059 (P : int -> Prop) : (term0 P) = (term1 P).
Proof. exact (EQ_MP (@lem2338275 P) (@lem2338274 P)). Qed.
Lemma lem2339060 (P : int -> Prop) (n : nat) : (term51 P n) = (term52 P n).
Proof. exact (@lem2339059 (term53 P n)). Qed.
Lemma lem2339061 (P : int -> Prop) (n : nat) (y : int) : (term54 P n y) = (term55 P n y).
Proof. exact (eq_refl (term54 P n y)). Qed.
Lemma lem2339062 (y : int) : (term7 y) = (term7 y).
Proof. exact (eq_refl (term7 y)). Qed.
Lemma lem2339063 (P : int -> Prop) (n : nat) (y : int) : (term56 P n y) = (term44 P n y).
Proof. exact (MK_COMB (@lem2339062 y) (@lem2339061 P n y)). Qed.
Lemma lem2339064 (P : int -> Prop) (n : nat) : (term57 P n) = (term48 P n).
Proof. exact (fun_ext (fun y : int => @lem2339063 P n y)). Qed.
Lemma lem2339065 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2339066 (P : int -> Prop) (n : nat) : (term51 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem2339065) (@lem2339064 P n)). Qed.
Lemma lem2339067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339068 (P : int -> Prop) (n : nat) : (term58 P n) = (term59 P n).
Proof. exact (MK_COMB (@lem2339067) (@lem2339066 P n)). Qed.
Lemma lem2339069 (P : int -> Prop) (n : nat) (n' : nat) : (term60 P n n') = (term61 P n n').
Proof. exact (eq_refl (term60 P n n')). Qed.
Lemma lem2339070 (P : int -> Prop) (n : nat) : (term62 P n) = (term63 P n).
Proof. exact (fun_ext (fun n' : nat => @lem2339069 P n n')). Qed.
Lemma lem2339071 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339072 (P : int -> Prop) (n : nat) : (term52 P n) = (term64 P n).
Proof. exact (MK_COMB (@lem2339071) (@lem2339070 P n)). Qed.
Lemma lem2339073 (P : int -> Prop) (n : nat) : ((term51 P n) = (term52 P n)) = ((term50 P n) = (term64 P n)).
Proof. exact (MK_COMB (@lem2339068 P n) (@lem2339072 P n)). Qed.
Lemma lem2339074 (P : int -> Prop) (n : nat) : (term50 P n) = (term64 P n).
Proof. exact (EQ_MP (@lem2339073 P n) (@lem2339060 P n)). Qed.
Lemma lem2339082 (m : nat) (n : nat) : (term65 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2338272 m n) (@lem2338271 m n)). Qed.
Lemma lem2339083 (n : nat) (n' : nat) : (term65 n n') = (Peano.le n n').
Proof. exact (@lem2339082 n n'). Qed.
Lemma lem2339084 (P : int -> Prop) (n' : nat) : (term66 P n') = (term66 P n').
Proof. exact (eq_refl (term66 P n')). Qed.
Lemma lem2339085 (P : int -> Prop) (n : nat) (n' : nat) : (term61 P n n') = (term67 P n n').
Proof. exact (MK_COMB (@lem2339084 P n') (@lem2339083 n n')). Qed.
Lemma lem2339088 (P : int -> Prop) (n : nat) : (term63 P n) = (term68 P n).
Proof. exact (fun_ext (fun n' : nat => @lem2339085 P n n')). Qed.
Lemma lem2339089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339090 (P : int -> Prop) (n : nat) : (term64 P n) = (term69 P n).
Proof. exact (MK_COMB (@lem2339089) (@lem2339088 P n)). Qed.
Lemma lem2339095 (P : int -> Prop) (n : nat) : (term50 P n) = (term69 P n).
Proof. exact (TRANS (@lem2339074 P n) (@lem2339090 P n)). Qed.
Lemma lem2339096 (P : int -> Prop) (n : nat) : (term49 P n) = (term69 P n).
Proof. exact (TRANS (@lem2339057 P n) (@lem2339095 P n)). Qed.
Lemma lem2339097 (P : int -> Prop) (n : nat) : (term70 P n) = (term70 P n).
Proof. exact (eq_refl (term70 P n)). Qed.
Lemma lem2339098 (P : int -> Prop) (n : nat) : (term71 P n) = (term72 P n).
Proof. exact (MK_COMB (@lem2339097 P n) (@lem2339096 P n)). Qed.
Lemma lem2339101 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2339102 (P : int -> Prop) (n : nat) : (term37 P n) = (term73 P n).
Proof. exact (MK_COMB (@lem2339101) (@lem2339098 P n)). Qed.
Lemma lem2339103 (P : int -> Prop) : (term39 P) = (term74 P).
Proof. exact (fun_ext (fun n : nat => @lem2339102 P n)). Qed.
Lemma lem2339104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339105 (P : int -> Prop) : (term40 P) = (term75 P).
Proof. exact (MK_COMB (@lem2339104) (@lem2339103 P)). Qed.
Lemma lem2339110 (P : int -> Prop) : (term33 P) = (term75 P).
Proof. exact (TRANS (@lem2339037 P) (@lem2339105 P)). Qed.
Lemma lem2339111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2339112 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (MK_COMB (@lem2339111) (@lem2339110 P)). Qed.
Lemma lem2339113 (P : int -> Prop) : ((term20 P) = (term76 P)) = ((term21 P) = (term77 P)).
Proof. exact (MK_COMB (@lem2339020 P) (@lem2339112 P)). Qed.
Lemma lem2339116 (P : int -> Prop) : ((term21 P) = (term77 P)) = ((term20 P) = (term76 P)).
Proof. exact (SYM (@lem2339113 P)). Qed.
Lemma lem2339120 {A : Type'} (P : A -> Prop) : (term78 A P) = (term79 A P).
Proof. exact (EQ_MP (@lem2338256 A P) (@lem2338255 A P)). Qed.
Lemma lem2339121 (P : nat -> Prop) : (term80 P) = (term81 P).
Proof. exact (@lem2339120 nat P). Qed.
Lemma lem2339122 (P : int -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem2339121 (term18 P)). Qed.
Lemma lem2339123 (P : int -> Prop) (n : nat) : (term84 P n) = (term16 P n).
Proof. exact (eq_refl (term84 P n)). Qed.
Lemma lem2339124 (P : int -> Prop) : (term85 P) = (term18 P).
Proof. exact (fun_ext (fun n : nat => @lem2339123 P n)). Qed.
Lemma lem2339125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339126 (P : int -> Prop) : (term86 P) = (term19 P).
Proof. exact (MK_COMB (@lem2339125) (@lem2339124 P)). Qed.
Lemma lem2339127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2339128 (P : int -> Prop) : (term82 P) = (term21 P).
Proof. exact (MK_COMB (@lem2339127) (@lem2339126 P)). Qed.
Lemma lem2339129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339130 (P : int -> Prop) : (term87 P) = (term23 P).
Proof. exact (MK_COMB (@lem2339129) (@lem2339128 P)). Qed.
Lemma lem2339131 (P : int -> Prop) (n : nat) : (term84 P n) = (term16 P n).
Proof. exact (eq_refl (term84 P n)). Qed.
Lemma lem2339132 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2339133 (P : int -> Prop) (n : nat) : (term88 P n) = (term89 P n).
Proof. exact (MK_COMB (@lem2339132) (@lem2339131 P n)). Qed.
Lemma lem2339134 (P : int -> Prop) : (term90 P) = (term91 P).
Proof. exact (fun_ext (fun n : nat => @lem2339133 P n)). Qed.
Lemma lem2339135 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2339136 (P : int -> Prop) : (term83 P) = (term92 P).
Proof. exact (MK_COMB (@lem2339135) (@lem2339134 P)). Qed.
Lemma lem2339137 (P : int -> Prop) : ((term82 P) = (term83 P)) = ((term21 P) = (term92 P)).
Proof. exact (MK_COMB (@lem2339130 P) (@lem2339136 P)). Qed.
Lemma lem2339138 (P : int -> Prop) : (term21 P) = (term92 P).
Proof. exact (EQ_MP (@lem2339137 P) (@lem2339122 P)). Qed.
Lemma lem2339144 (t : Prop) : (term93 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem2339145 (P : int -> Prop) (n : nat) : (term89 P n) = (term94 P n).
Proof. exact (@lem2339144 (term94 P n)). Qed.
Lemma lem2339146 (P : int -> Prop) : (term91 P) = (term95 P).
Proof. exact (fun_ext (fun n : nat => @lem2339145 P n)). Qed.
Lemma lem2339147 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2339148 (P : int -> Prop) : (term92 P) = (term96 P).
Proof. exact (MK_COMB (@lem2339147) (@lem2339146 P)). Qed.
Lemma lem2339153 (P : int -> Prop) : (term21 P) = (term96 P).
Proof. exact (TRANS (@lem2339138 P) (@lem2339148 P)). Qed.
Lemma lem2339154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339155 (P : int -> Prop) : (term23 P) = (term97 P).
Proof. exact (MK_COMB (@lem2339154) (@lem2339153 P)). Qed.
Lemma lem2339157 {A : Type'} (P : A -> Prop) : (term78 A P) = (term79 A P).
Proof. exact (EQ_MP (@lem2338256 A P) (@lem2338255 A P)). Qed.
Lemma lem2339158 (P : nat -> Prop) : (term80 P) = (term81 P).
Proof. exact (@lem2339157 nat P). Qed.
Lemma lem2339159 (P : int -> Prop) : (term98 P) = (term99 P).
Proof. exact (@lem2339158 (term74 P)). Qed.
Lemma lem2339160 (P : int -> Prop) (n : nat) : (term100 P n) = (term73 P n).
Proof. exact (eq_refl (term100 P n)). Qed.
Lemma lem2339161 (P : int -> Prop) : (term101 P) = (term74 P).
Proof. exact (fun_ext (fun n : nat => @lem2339160 P n)). Qed.
Lemma lem2339162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339163 (P : int -> Prop) : (term102 P) = (term75 P).
Proof. exact (MK_COMB (@lem2339162) (@lem2339161 P)). Qed.
Lemma lem2339164 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2339165 (P : int -> Prop) : (term98 P) = (term77 P).
Proof. exact (MK_COMB (@lem2339164) (@lem2339163 P)). Qed.
Lemma lem2339166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339167 (P : int -> Prop) : (term103 P) = (term104 P).
Proof. exact (MK_COMB (@lem2339166) (@lem2339165 P)). Qed.
Lemma lem2339168 (P : int -> Prop) (n : nat) : (term100 P n) = (term73 P n).
Proof. exact (eq_refl (term100 P n)). Qed.
Lemma lem2339169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2339170 (P : int -> Prop) (n : nat) : (term105 P n) = (term106 P n).
Proof. exact (MK_COMB (@lem2339169) (@lem2339168 P n)). Qed.
Lemma lem2339171 (P : int -> Prop) : (term107 P) = (term108 P).
Proof. exact (fun_ext (fun n : nat => @lem2339170 P n)). Qed.
Lemma lem2339172 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2339173 (P : int -> Prop) : (term99 P) = (term109 P).
Proof. exact (MK_COMB (@lem2339172) (@lem2339171 P)). Qed.
Lemma lem2339174 (P : int -> Prop) : ((term98 P) = (term99 P)) = ((term77 P) = (term109 P)).
Proof. exact (MK_COMB (@lem2339167 P) (@lem2339173 P)). Qed.
Lemma lem2339175 (P : int -> Prop) : (term77 P) = (term109 P).
Proof. exact (EQ_MP (@lem2339174 P) (@lem2339159 P)). Qed.
Lemma lem2339181 (t : Prop) : (term93 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem2339182 (P : int -> Prop) (n : nat) : (term106 P n) = (term72 P n).
Proof. exact (@lem2339181 (term72 P n)). Qed.
Lemma lem2339191 (P : int -> Prop) : (term108 P) = (term110 P).
Proof. exact (fun_ext (fun n : nat => @lem2339182 P n)). Qed.
Lemma lem2339192 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2339193 (P : int -> Prop) : (term109 P) = (term111 P).
Proof. exact (MK_COMB (@lem2339192) (@lem2339191 P)). Qed.
Lemma lem2339198 (P : int -> Prop) : (term77 P) = (term111 P).
Proof. exact (TRANS (@lem2339175 P) (@lem2339193 P)). Qed.
Lemma lem2339199 (P : int -> Prop) : ((term21 P) = (term77 P)) = ((term96 P) = (term111 P)).
Proof. exact (MK_COMB (@lem2339155 P) (@lem2339198 P)). Qed.
Lemma lem2339202 (P : int -> Prop) : ((term96 P) = (term111 P)) = ((term21 P) = (term77 P)).
Proof. exact (SYM (@lem2339199 P)). Qed.
Lemma lem2339204 (P : nat -> Prop) : (term112 P) = (term113 P).
Proof. exact (EQ_MP (@lem2338253 P) (@lem2338252 P)). Qed.
Lemma lem2339205 (P : int -> Prop) : (term114 P) = (term115 P).
Proof. exact (@lem2339204 (term95 P)). Qed.
Lemma lem2339206 (P : int -> Prop) (n : nat) : (term116 P n) = (term94 P n).
Proof. exact (eq_refl (term116 P n)). Qed.
Lemma lem2339207 (P : int -> Prop) : (term117 P) = (term95 P).
Proof. exact (fun_ext (fun n : nat => @lem2339206 P n)). Qed.
Lemma lem2339208 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2339209 (P : int -> Prop) : (term114 P) = (term96 P).
Proof. exact (MK_COMB (@lem2339208) (@lem2339207 P)). Qed.
Lemma lem2339210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339211 (P : int -> Prop) : (term118 P) = (term97 P).
Proof. exact (MK_COMB (@lem2339210) (@lem2339209 P)). Qed.
Lemma lem2339212 (P : int -> Prop) (n : nat) : (term116 P n) = (term94 P n).
Proof. exact (eq_refl (term116 P n)). Qed.
Lemma lem2339213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2339214 (P : int -> Prop) (n : nat) : (term119 P n) = (term70 P n).
Proof. exact (MK_COMB (@lem2339213) (@lem2339212 P n)). Qed.
Lemma lem2339215 (P : int -> Prop) (m : nat) : (term116 P m) = (term94 P m).
Proof. exact (eq_refl (term116 P m)). Qed.
Lemma lem2339216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2339217 (P : int -> Prop) (m : nat) : (term120 P m) = (term16 P m).
Proof. exact (MK_COMB (@lem2339216) (@lem2339215 P m)). Qed.
Lemma lem2339218 (m : nat) (n : nat) : (term121 m n) = (term121 m n).
Proof. exact (eq_refl (term121 m n)). Qed.
Lemma lem2339219 (n : nat) (P : int -> Prop) (m : nat) : (term122 n P m) = (term123 n P m).
Proof. exact (MK_COMB (@lem2339218 m n) (@lem2339217 P m)). Qed.
Lemma lem2339220 (n : nat) (P : int -> Prop) : (term124 n P) = (term125 n P).
Proof. exact (fun_ext (fun m : nat => @lem2339219 n P m)). Qed.
Lemma lem2339221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339222 (n : nat) (P : int -> Prop) : (term126 n P) = (term127 n P).
Proof. exact (MK_COMB (@lem2339221) (@lem2339220 n P)). Qed.
Lemma lem2339223 (n : nat) (P : int -> Prop) : (term128 n P) = (term129 n P).
Proof. exact (MK_COMB (@lem2339214 P n) (@lem2339222 n P)). Qed.
Lemma lem2339224 (P : int -> Prop) : (term130 P) = (term131 P).
Proof. exact (fun_ext (fun n : nat => @lem2339223 n P)). Qed.
Lemma lem2339225 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2339226 (P : int -> Prop) : (term115 P) = (term132 P).
Proof. exact (MK_COMB (@lem2339225) (@lem2339224 P)). Qed.
Lemma lem2339227 (P : int -> Prop) : ((term114 P) = (term115 P)) = ((term96 P) = (term132 P)).
Proof. exact (MK_COMB (@lem2339211 P) (@lem2339226 P)). Qed.
Lemma lem2339228 (P : int -> Prop) : (term96 P) = (term132 P).
Proof. exact (EQ_MP (@lem2339227 P) (@lem2339205 P)). Qed.
Lemma lem2339229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339230 (P : int -> Prop) : (term97 P) = (term133 P).
Proof. exact (MK_COMB (@lem2339229) (@lem2339228 P)). Qed.
Lemma lem2339231 (P : int -> Prop) : (term111 P) = (term111 P).
Proof. exact (eq_refl (term111 P)). Qed.
Lemma lem2339232 (P : int -> Prop) : ((term96 P) = (term111 P)) = ((term132 P) = (term111 P)).
Proof. exact (MK_COMB (@lem2339230 P) (@lem2339231 P)). Qed.
Lemma lem2339233 (P : int -> Prop) : ((term132 P) = (term111 P)) = ((term96 P) = (term111 P)).
Proof. exact (SYM (@lem2339232 P)). Qed.
Lemma lem2339249 (m : nat) (n : nat) : (Peano.lt n m) = (term134 m n).
Proof. exact (EQ_MP (@lem2338250 m n) (@lem2338249 m n)). Qed.
Lemma lem2339250 (n : nat) (m : nat) : (Peano.lt m n) = (term134 n m).
Proof. exact (@lem2339249 n m). Qed.
Lemma lem2339251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2339252 (n : nat) (m : nat) : (term121 m n) = (term135 n m).
Proof. exact (MK_COMB (@lem2339251) (@lem2339250 n m)). Qed.
Lemma lem2339253 (P : int -> Prop) (m : nat) : (term16 P m) = (term16 P m).
Proof. exact (eq_refl (term16 P m)). Qed.
Lemma lem2339254 (n : nat) (P : int -> Prop) (m : nat) : (term123 n P m) = (term136 n P m).
Proof. exact (MK_COMB (@lem2339252 n m) (@lem2339253 P m)). Qed.
Lemma lem2339256 (t2 : Prop) (t1 : Prop) : (term137 t1 t2) = (t2 -> t1).
Proof. exact (EQ_MP (@lem2338244 t2 t1) (@lem2338243 t1 t2)). Qed.
Lemma lem2339257 (P : int -> Prop) (n : nat) (m : nat) : (term136 n P m) = (term67 P n m).
Proof. exact (@lem2339256 (term94 P m) (Peano.le n m)). Qed.
Lemma lem2339260 (P : int -> Prop) (n : nat) (m : nat) : (term123 n P m) = (term67 P n m).
Proof. exact (TRANS (@lem2339254 n P m) (@lem2339257 P n m)). Qed.
Lemma lem2339261 (P : int -> Prop) (n : nat) : (term125 n P) = (term68 P n).
Proof. exact (fun_ext (fun m : nat => @lem2339260 P n m)). Qed.
Lemma lem2339262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2339263 (P : int -> Prop) (n : nat) : (term127 n P) = (term69 P n).
Proof. exact (MK_COMB (@lem2339262) (@lem2339261 P n)). Qed.
Lemma lem2339268 (P : int -> Prop) (n : nat) : (term70 P n) = (term70 P n).
Proof. exact (eq_refl (term70 P n)). Qed.
Lemma lem2339269 (P : int -> Prop) (n : nat) : (term129 n P) = (term72 P n).
Proof. exact (MK_COMB (@lem2339268 P n) (@lem2339263 P n)). Qed.
Lemma lem2339272 (P : int -> Prop) : (term131 P) = (term110 P).
Proof. exact (fun_ext (fun n : nat => @lem2339269 P n)). Qed.
Lemma lem2339273 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2339274 (P : int -> Prop) : (term132 P) = (term111 P).
Proof. exact (MK_COMB (@lem2339273) (@lem2339272 P)). Qed.
Lemma lem2339279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339280 (P : int -> Prop) : (term133 P) = (term138 P).
Proof. exact (MK_COMB (@lem2339279) (@lem2339274 P)). Qed.
Lemma lem2339293 (P : int -> Prop) : (term111 P) = (term111 P).
Proof. exact (eq_refl (term111 P)). Qed.
Lemma lem2339294 (P : int -> Prop) : ((term132 P) = (term111 P)) = ((term111 P) = (term111 P)).
Proof. exact (MK_COMB (@lem2339280 P) (@lem2339293 P)). Qed.
Lemma lem2339296 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2339297 (x : Prop) : (x = x) = True.
Proof. exact (@lem2339296 Prop x). Qed.
Lemma lem2339298 (P : int -> Prop) : ((term111 P) = (term111 P)) = True.
Proof. exact (@lem2339297 (term111 P)). Qed.
Lemma lem2339301 (P : int -> Prop) : (term139 P) = (term139 P).
Proof. exact (eq_refl (term139 P)). Qed.
Lemma lem2339302 (P : int -> Prop) : (term139 P) = (((term111 P) = (term111 P)) = True).
Proof. exact (eq_refl (term139 P)). Qed.
Lemma lem2339303 (P : int -> Prop) : (term140 P) = (term140 P).
Proof. exact (eq_refl (term140 P)). Qed.
Lemma lem2339304 (P : int -> Prop) : ((term139 P) = (term139 P)) = ((term139 P) = (((term111 P) = (term111 P)) = True)).
Proof. exact (MK_COMB (@lem2339303 P) (@lem2339302 P)). Qed.
Lemma lem2339305 (P : int -> Prop) : (term139 P) = (((term111 P) = (term111 P)) = True).
Proof. exact (eq_refl (term139 P)). Qed.
Lemma lem2339306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2339307 (P : int -> Prop) : (term140 P) = (term141 P).
Proof. exact (MK_COMB (@lem2339306) (@lem2339305 P)). Qed.
Lemma lem2339308 (P : int -> Prop) : (((term111 P) = (term111 P)) = True) = (((term111 P) = (term111 P)) = True).
Proof. exact (eq_refl (((term111 P) = (term111 P)) = True)). Qed.
Lemma lem2339309 (P : int -> Prop) : ((term139 P) = (((term111 P) = (term111 P)) = True)) = ((((term111 P) = (term111 P)) = True) = (((term111 P) = (term111 P)) = True)).
Proof. exact (MK_COMB (@lem2339307 P) (@lem2339308 P)). Qed.
Lemma lem2339310 (P : int -> Prop) : ((term139 P) = (term139 P)) = ((((term111 P) = (term111 P)) = True) = (((term111 P) = (term111 P)) = True)).
Proof. exact (TRANS (@lem2339304 P) (@lem2339309 P)). Qed.
Lemma lem2339311 (P : int -> Prop) : (((term111 P) = (term111 P)) = True) = (((term111 P) = (term111 P)) = True).
Proof. exact (EQ_MP (@lem2339310 P) (@lem2339301 P)). Qed.
Lemma lem2339312 (P : int -> Prop) : ((term111 P) = (term111 P)) = True.
Proof. exact (EQ_MP (@lem2339311 P) (@lem2339298 P)). Qed.
Lemma lem2339313 (P : int -> Prop) : ((term132 P) = (term111 P)) = True.
Proof. exact (TRANS (@lem2339294 P) (@lem2339312 P)). Qed.
Lemma lem2339314 (P : int -> Prop) : True = ((term132 P) = (term111 P)).
Proof. exact (SYM (@lem2339313 P)). Qed.
Lemma lem2339315 (P : int -> Prop) : (term132 P) = (term111 P).
Proof. exact (EQ_MP (@lem2339314 P) (@lem0)). Qed.
Lemma lem2339316 (P : int -> Prop) : (term96 P) = (term111 P).
Proof. exact (EQ_MP (@lem2339233 P) (@lem2339315 P)). Qed.
Lemma lem2339317 (P : int -> Prop) : (term21 P) = (term77 P).
Proof. exact (EQ_MP (@lem2339202 P) (@lem2339316 P)). Qed.
Lemma lem2339318 (P : int -> Prop) : (term20 P) = (term76 P).
Proof. exact (EQ_MP (@lem2339116 P) (@lem2339317 P)). Qed.
