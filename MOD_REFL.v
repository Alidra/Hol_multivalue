Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_REFL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MOD_EQ_0_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem199836 (m : nat) : term0 m.
Proof. exact (@lem199160 m). Qed.
Lemma lem199837 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem199838 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem199837 m) (@lem199836 m)). Qed.
Lemma lem199839 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem199838 m n). Qed.
Lemma lem199840 (m : nat) (n : nat) : (term2 m n) = (((Nat.modulo m n) = (NUMERAL 0)) = (term3 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem199847 (m : nat) (n : nat) : ((Nat.modulo m n) = (NUMERAL 0)) = (term3 m n).
Proof. exact (EQ_MP (@lem199840 m n) (@lem199839 m n)). Qed.
Lemma lem199848 (n : nat) : ((Nat.modulo n n) = (NUMERAL 0)) = (term4 n).
Proof. exact (@lem199847 n n). Qed.
Lemma lem199855 : term5 = term6.
Proof. exact (fun_ext (fun n : nat => @lem199848 n)). Qed.
Lemma lem199862 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199863 : term7 = term8.
Proof. exact (MK_COMB (@lem199862) (@lem199855)). Qed.
Lemma lem199874 : term8 = term7.
Proof. exact (SYM (@lem199863)). Qed.
Lemma lem199876 (p : Prop) : p = (term9 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem199877 : term8 = term10.
Proof. exact (@lem199876 term8). Qed.
Lemma lem199878 : term10 = term8.
Proof. exact (SYM (@lem199877)). Qed.
Lemma lem199879 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem199882 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem199883 : term13.
Proof. exact (fun h0 : term12 => @lem199882 h0). Qed.
Lemma lem199884 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem199885 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem199886 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem199884 h2 (@lem199885 h1)). Qed.
Lemma lem199887 (h1 : term12) : term14.
Proof. exact (fun h0 : term13 => @lem199886 h1 h0). Qed.
Lemma lem199888 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem199889 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem199887 h1 (@lem199888 h2)). Qed.
Lemma lem199890 (h1 : term13) : term13.
Proof. exact (fun h0 : term12 => @lem199889 h0 h1). Qed.
Lemma lem199891 : term15.
Proof. exact (fun h0 : term13 => @lem199890 h0). Qed.
Lemma lem199894 : term13.
Proof. exact (@lem199891 (@lem199883)). Qed.
Lemma lem199906 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem199907 : term16 = term17.
Proof. exact (@lem199906 term18). Qed.
Lemma lem199950 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem199957 : term12 = term20.
Proof. exact (MK_COMB (@lem199950) (@lem199907)). Qed.
Lemma lem199958 (m : nat) (n : nat) : ((term21 m n) = (term22 m n)) = ((term21 m n) = (term22 m n)).
Proof. exact (eq_refl ((term21 m n) = (term22 m n))). Qed.
Lemma lem199959 (m : nat) : (term23 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem199958 m n)). Qed.
Lemma lem199960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199961 (m : nat) : (term24 m) = (term24 m).
Proof. exact (MK_COMB (@lem199960) (@lem199959 m)). Qed.
Lemma lem199962 : term25 = term25.
Proof. exact (fun_ext (fun m : nat => @lem199961 m)). Qed.
Lemma lem199963 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199964 : term26 = term26.
Proof. exact (MK_COMB (@lem199963) (@lem199962)). Qed.
Lemma lem199965 (m : nat) (n : nat) : ((term27 m n) = (term28 m n)) = ((term27 m n) = (term28 m n)).
Proof. exact (eq_refl ((term27 m n) = (term28 m n))). Qed.
Lemma lem199966 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem199965 m n)). Qed.
Lemma lem199967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199968 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem199967) (@lem199966 m)). Qed.
Lemma lem199969 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem199968 m)). Qed.
Lemma lem199970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199971 : term32 = term32.
Proof. exact (MK_COMB (@lem199970) (@lem199969)). Qed.
Lemma lem199972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem199973 : term33 = term33.
Proof. exact (MK_COMB (@lem199972) (@lem199971)). Qed.
Lemma lem199974 : term34 = term34.
Proof. exact (MK_COMB (@lem199973) (@lem199964)). Qed.
Lemma lem199975 (m : nat) : ((term35 m) = m) = ((term35 m) = m).
Proof. exact (eq_refl ((term35 m) = m)). Qed.
Lemma lem199976 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem199975 m)). Qed.
Lemma lem199977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199978 : term37 = term37.
Proof. exact (MK_COMB (@lem199977) (@lem199976)). Qed.
Lemma lem199979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem199980 : term38 = term38.
Proof. exact (MK_COMB (@lem199979) (@lem199978)). Qed.
Lemma lem199981 : term39 = term39.
Proof. exact (MK_COMB (@lem199980) (@lem199974)). Qed.
Lemma lem199982 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem199983 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem199982 n)). Qed.
Lemma lem199984 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199985 : term42 = term42.
Proof. exact (MK_COMB (@lem199984) (@lem199983)). Qed.
Lemma lem199986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem199987 : term43 = term43.
Proof. exact (MK_COMB (@lem199986) (@lem199985)). Qed.
Lemma lem199988 : term44 = term44.
Proof. exact (MK_COMB (@lem199987) (@lem199981)). Qed.
Lemma lem199989 (m : nat) : ((term45 m) = (NUMERAL 0)) = ((term45 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term45 m) = (NUMERAL 0))). Qed.
Lemma lem199990 : term46 = term46.
Proof. exact (fun_ext (fun m : nat => @lem199989 m)). Qed.
Lemma lem199991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199992 : term47 = term47.
Proof. exact (MK_COMB (@lem199991) (@lem199990)). Qed.
Lemma lem199993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem199994 : term48 = term48.
Proof. exact (MK_COMB (@lem199993) (@lem199992)). Qed.
Lemma lem199995 : term49 = term49.
Proof. exact (MK_COMB (@lem199994) (@lem199988)). Qed.
Lemma lem199996 (n : nat) : ((term50 n) = (NUMERAL 0)) = ((term50 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term50 n) = (NUMERAL 0))). Qed.
Lemma lem199997 : term51 = term51.
Proof. exact (fun_ext (fun n : nat => @lem199996 n)). Qed.
Lemma lem199998 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem199999 : term52 = term52.
Proof. exact (MK_COMB (@lem199998) (@lem199997)). Qed.
Lemma lem200000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200001 : term53 = term53.
Proof. exact (MK_COMB (@lem200000) (@lem199999)). Qed.
Lemma lem200002 : term18 = term18.
Proof. exact (MK_COMB (@lem200001) (@lem199995)). Qed.
Lemma lem200003 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem200004 : term17 = term17.
Proof. exact (MK_COMB (@lem200003) (@lem200002)). Qed.
Lemma lem200005 (q : nat) (n : nat) : (n = (Nat.mul q n)) = (n = (Nat.mul q n)).
Proof. exact (eq_refl (n = (Nat.mul q n))). Qed.
Lemma lem200006 (n : nat) : (term54 n) = (term54 n).
Proof. exact (fun_ext (fun q : nat => @lem200005 q n)). Qed.
Lemma lem200007 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem200008 (n : nat) : (term4 n) = (term4 n).
Proof. exact (MK_COMB (@lem200007) (@lem200006 n)). Qed.
Lemma lem200009 : term6 = term6.
Proof. exact (fun_ext (fun n : nat => @lem200008 n)). Qed.
Lemma lem200010 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200011 : term8 = term8.
Proof. exact (MK_COMB (@lem200010) (@lem200009)). Qed.
Lemma lem200012 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem200013 : term11 = term11.
Proof. exact (MK_COMB (@lem200012) (@lem200011)). Qed.
Lemma lem200014 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem200015 : term19 = term19.
Proof. exact (MK_COMB (@lem200014) (@lem200013)). Qed.
Lemma lem200016 : term20 = term20.
Proof. exact (MK_COMB (@lem200015) (@lem200004)). Qed.
Lemma lem200091 : term12 = term20.
Proof. exact (TRANS (@lem199957) (@lem200016)). Qed.
Lemma lem200092 : term20 = term12.
Proof. exact (SYM (@lem200091)). Qed.
Lemma lem200093 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem200094 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem200096 (P : nat -> Prop) : (term55 P) = (term56 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem200097 (n : nat) : (term57 n) = (term58 n).
Proof. exact (@lem200096 (term54 n)). Qed.
Lemma lem200098 (q : nat) (n : nat) : (term59 n q) = (n = (Nat.mul q n)).
Proof. exact (eq_refl (term59 n q)). Qed.
Lemma lem200099 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem200101 (q : nat) (n : nat) : (term60 n q) = (term61 q n).
Proof. exact (MK_COMB (@lem200099) (@lem200098 q n)). Qed.
Lemma lem200102 (n : nat) : (term62 n) = (term63 n).
Proof. exact (fun_ext (fun q : nat => @lem200101 q n)). Qed.
Lemma lem200103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200104 (n : nat) : (term58 n) = (term64 n).
Proof. exact (MK_COMB (@lem200103) (@lem200102 n)). Qed.
Lemma lem200105 (n : nat) : (term57 n) = (term64 n).
Proof. exact (TRANS (@lem200097 n) (@lem200104 n)). Qed.
Lemma lem200106 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem200107 : term11 = term67.
Proof. exact (@lem200106 term6). Qed.
Lemma lem200108 (n : nat) : (term68 n) = (term4 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem200109 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem200110 (n : nat) : (term69 n) = (term57 n).
Proof. exact (MK_COMB (@lem200109) (@lem200108 n)). Qed.
Lemma lem200111 (n : nat) : (term69 n) = (term64 n).
Proof. exact (TRANS (@lem200110 n) (@lem200105 n)). Qed.
Lemma lem200112 : term70 = term71.
Proof. exact (fun_ext (fun n : nat => @lem200111 n)). Qed.
Lemma lem200113 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem200114 : term67 = term72.
Proof. exact (MK_COMB (@lem200113) (@lem200112)). Qed.
Lemma lem200127 : term11 = term72.
Proof. exact (TRANS (@lem200107) (@lem200114)). Qed.
Lemma lem200128 (h1 : term11) : term72.
Proof. exact (EQ_MP (@lem200127) (@lem200093 h1)). Qed.
Lemma lem200129 (n : nat) : ((term50 n) = (NUMERAL 0)) = ((term50 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term50 n) = (NUMERAL 0))). Qed.
Lemma lem200130 : term51 = term51.
Proof. exact (fun_ext (fun n : nat => @lem200129 n)). Qed.
Lemma lem200131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200132 : term52 = term52.
Proof. exact (MK_COMB (@lem200131) (@lem200130)). Qed.
Lemma lem200133 (m : nat) : ((term45 m) = (NUMERAL 0)) = ((term45 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term45 m) = (NUMERAL 0))). Qed.
Lemma lem200134 : term46 = term46.
Proof. exact (fun_ext (fun m : nat => @lem200133 m)). Qed.
Lemma lem200135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200136 : term47 = term47.
Proof. exact (MK_COMB (@lem200135) (@lem200134)). Qed.
Lemma lem200137 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem200138 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem200137 n)). Qed.
Lemma lem200139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200140 : term42 = term42.
Proof. exact (MK_COMB (@lem200139) (@lem200138)). Qed.
Lemma lem200141 (m : nat) : ((term35 m) = m) = ((term35 m) = m).
Proof. exact (eq_refl ((term35 m) = m)). Qed.
Lemma lem200142 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem200141 m)). Qed.
Lemma lem200143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200144 : term37 = term37.
Proof. exact (MK_COMB (@lem200143) (@lem200142)). Qed.
Lemma lem200145 (m : nat) (n : nat) : ((term27 m n) = (term28 m n)) = ((term27 m n) = (term28 m n)).
Proof. exact (eq_refl ((term27 m n) = (term28 m n))). Qed.
Lemma lem200146 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem200145 m n)). Qed.
Lemma lem200147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200148 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem200147) (@lem200146 m)). Qed.
Lemma lem200149 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem200148 m)). Qed.
Lemma lem200150 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200151 : term32 = term32.
Proof. exact (MK_COMB (@lem200150) (@lem200149)). Qed.
Lemma lem200152 (m : nat) (n : nat) : ((term21 m n) = (term22 m n)) = ((term21 m n) = (term22 m n)).
Proof. exact (eq_refl ((term21 m n) = (term22 m n))). Qed.
Lemma lem200153 (m : nat) : (term23 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem200152 m n)). Qed.
Lemma lem200154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200155 (m : nat) : (term24 m) = (term24 m).
Proof. exact (MK_COMB (@lem200154) (@lem200153 m)). Qed.
Lemma lem200156 : term25 = term25.
Proof. exact (fun_ext (fun m : nat => @lem200155 m)). Qed.
Lemma lem200157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200158 : term26 = term26.
Proof. exact (MK_COMB (@lem200157) (@lem200156)). Qed.
Lemma lem200159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200160 : term33 = term33.
Proof. exact (MK_COMB (@lem200159) (@lem200151)). Qed.
Lemma lem200161 : term34 = term34.
Proof. exact (MK_COMB (@lem200160) (@lem200158)). Qed.
Lemma lem200162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200163 : term38 = term38.
Proof. exact (MK_COMB (@lem200162) (@lem200144)). Qed.
Lemma lem200164 : term39 = term39.
Proof. exact (MK_COMB (@lem200163) (@lem200161)). Qed.
Lemma lem200165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200166 : term43 = term43.
Proof. exact (MK_COMB (@lem200165) (@lem200140)). Qed.
Lemma lem200167 : term44 = term44.
Proof. exact (MK_COMB (@lem200166) (@lem200164)). Qed.
Lemma lem200168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200169 : term48 = term48.
Proof. exact (MK_COMB (@lem200168) (@lem200136)). Qed.
Lemma lem200170 : term49 = term49.
Proof. exact (MK_COMB (@lem200169) (@lem200167)). Qed.
Lemma lem200171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200172 : term53 = term53.
Proof. exact (MK_COMB (@lem200171) (@lem200132)). Qed.
Lemma lem200209 : term18 = term18.
Proof. exact (MK_COMB (@lem200172) (@lem200170)). Qed.
Lemma lem200210 (h1 : term18) : term18.
Proof. exact (EQ_MP (@lem200209) (@lem200094 h1)). Qed.
Lemma lem200211 (n : nat) (h1 : term64 n) : term64 n.
Proof. exact (h1). Qed.
Lemma lem200230 (m : nat) (n : nat) : ((term21 m n) = (term22 m n)) = ((term21 m n) = (term22 m n)).
Proof. exact (eq_refl ((term21 m n) = (term22 m n))). Qed.
Lemma lem200231 (m : nat) : (term23 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem200230 m n)). Qed.
Lemma lem200232 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200233 (m : nat) : (term24 m) = (term24 m).
Proof. exact (MK_COMB (@lem200232) (@lem200231 m)). Qed.
Lemma lem200234 : term25 = term25.
Proof. exact (fun_ext (fun m : nat => @lem200233 m)). Qed.
Lemma lem200235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200236 : term26 = term26.
Proof. exact (MK_COMB (@lem200235) (@lem200234)). Qed.
Lemma lem200255 (m : nat) (n : nat) : ((term27 m n) = (term28 m n)) = ((term27 m n) = (term28 m n)).
Proof. exact (eq_refl ((term27 m n) = (term28 m n))). Qed.
Lemma lem200256 (m : nat) : (term29 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem200255 m n)). Qed.
Lemma lem200257 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200258 (m : nat) : (term30 m) = (term30 m).
Proof. exact (MK_COMB (@lem200257) (@lem200256 m)). Qed.
Lemma lem200259 : term31 = term31.
Proof. exact (fun_ext (fun m : nat => @lem200258 m)). Qed.
Lemma lem200260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200261 : term32 = term32.
Proof. exact (MK_COMB (@lem200260) (@lem200259)). Qed.
Lemma lem200262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200263 : term33 = term33.
Proof. exact (MK_COMB (@lem200262) (@lem200261)). Qed.
Lemma lem200264 : term34 = term34.
Proof. exact (MK_COMB (@lem200263) (@lem200236)). Qed.
Lemma lem200277 (m : nat) : ((term35 m) = m) = ((term35 m) = m).
Proof. exact (eq_refl ((term35 m) = m)). Qed.
Lemma lem200278 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem200277 m)). Qed.
Lemma lem200279 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200280 : term37 = term37.
Proof. exact (MK_COMB (@lem200279) (@lem200278)). Qed.
Lemma lem200281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200282 : term38 = term38.
Proof. exact (MK_COMB (@lem200281) (@lem200280)). Qed.
Lemma lem200283 : term39 = term39.
Proof. exact (MK_COMB (@lem200282) (@lem200264)). Qed.
Lemma lem200296 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem200297 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem200296 n)). Qed.
Lemma lem200298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200299 : term42 = term42.
Proof. exact (MK_COMB (@lem200298) (@lem200297)). Qed.
Lemma lem200300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200301 : term43 = term43.
Proof. exact (MK_COMB (@lem200300) (@lem200299)). Qed.
Lemma lem200302 : term44 = term44.
Proof. exact (MK_COMB (@lem200301) (@lem200283)). Qed.
Lemma lem200315 (m : nat) : ((term45 m) = (NUMERAL 0)) = ((term45 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term45 m) = (NUMERAL 0))). Qed.
Lemma lem200316 : term46 = term46.
Proof. exact (fun_ext (fun m : nat => @lem200315 m)). Qed.
Lemma lem200317 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200318 : term47 = term47.
Proof. exact (MK_COMB (@lem200317) (@lem200316)). Qed.
Lemma lem200319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200320 : term48 = term48.
Proof. exact (MK_COMB (@lem200319) (@lem200318)). Qed.
Lemma lem200321 : term49 = term49.
Proof. exact (MK_COMB (@lem200320) (@lem200302)). Qed.
Lemma lem200334 (n : nat) : ((term50 n) = (NUMERAL 0)) = ((term50 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term50 n) = (NUMERAL 0))). Qed.
Lemma lem200335 : term51 = term51.
Proof. exact (fun_ext (fun n : nat => @lem200334 n)). Qed.
Lemma lem200336 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200337 : term52 = term52.
Proof. exact (MK_COMB (@lem200336) (@lem200335)). Qed.
Lemma lem200338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200339 : term53 = term53.
Proof. exact (MK_COMB (@lem200338) (@lem200337)). Qed.
Lemma lem200340 : term18 = term18.
Proof. exact (MK_COMB (@lem200339) (@lem200321)). Qed.
Lemma lem200341 (h1 : term18) : term18.
Proof. exact (EQ_MP (@lem200340) (@lem200210 h1)). Qed.
Lemma lem200352 (q : nat) (n : nat) : (term61 q n) = (term61 q n).
Proof. exact (eq_refl (term61 q n)). Qed.
Lemma lem200353 (n : nat) : (term63 n) = (term63 n).
Proof. exact (fun_ext (fun q : nat => @lem200352 q n)). Qed.
Lemma lem200354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200355 (n : nat) : (term64 n) = (term64 n).
Proof. exact (MK_COMB (@lem200354) (@lem200353 n)). Qed.
Lemma lem200356 (n : nat) (h1 : term64 n) : term64 n.
Proof. exact (EQ_MP (@lem200355 n) (@lem200211 n h1)). Qed.
Lemma lem200357 (h1 : term18) : term49.
Proof. exact (proj2 (@lem200341 h1)). Qed.
Lemma lem200359 (h1 : term18) : term44.
Proof. exact (proj2 (@lem200357 h1)). Qed.
Lemma lem200362 (h1 : term18) : term42.
Proof. exact (proj1 (@lem200359 h1)). Qed.
Lemma lem200368 (q : nat) (n : nat) : (term61 q n) = (term61 q n).
Proof. exact (eq_refl (term61 q n)). Qed.
Lemma lem200369 (n : nat) : (term63 n) = (term63 n).
Proof. exact (fun_ext (fun q : nat => @lem200368 q n)). Qed.
Lemma lem200370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200372 (n : nat) : (term64 n) = (term64 n).
Proof. exact (MK_COMB (@lem200370) (@lem200369 n)). Qed.
Lemma lem200373 (n : nat) (h1 : term64 n) : term64 n.
Proof. exact (EQ_MP (@lem200372 n) (@lem200356 n h1)). Qed.
Lemma lem200389 (n : nat) : ((term40 n) = n) = ((term40 n) = n).
Proof. exact (eq_refl ((term40 n) = n)). Qed.
Lemma lem200390 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem200389 n)). Qed.
Lemma lem200391 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem200393 : term42 = term42.
Proof. exact (MK_COMB (@lem200391) (@lem200390)). Qed.
Lemma lem200394 (h1 : term18) : term42.
Proof. exact (EQ_MP (@lem200393) (@lem200362 h1)). Qed.
Lemma lem200422 (_4027 : nat) (n : nat) (h1 : term64 n) : term73 n _4027.
Proof. exact (@lem200373 n h1 _4027). Qed.
Lemma lem200423 (_4027 : nat) (n : nat) : (term73 n _4027) = (term61 _4027 n).
Proof. exact (eq_refl (term73 n _4027)). Qed.
Lemma lem200431 (_4030 : nat) (h1 : term18) : term74 _4030.
Proof. exact (@lem200394 h1 _4030). Qed.
Lemma lem200432 (_4030 : nat) : (term74 _4030) = ((term40 _4030) = _4030).
Proof. exact (eq_refl (term74 _4030)). Qed.
Lemma lem200450 (_4027 : nat) (n : nat) (h1 : term64 n) : term61 _4027 n.
Proof. exact (EQ_MP (@lem200423 _4027 n) (@lem200422 _4027 n h1)). Qed.
Lemma lem200518 (x : nat) (y : nat) (z : nat) : term75 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem200520 (_4030 : nat) (h1 : term18) : (term40 _4030) = _4030.
Proof. exact (EQ_MP (@lem200432 _4030) (@lem200431 _4030 h1)). Qed.
Lemma lem200521 (n : nat) (h1 : term18) : (term40 n) = n.
Proof. exact (@lem200520 n h1). Qed.
Lemma lem200522 (n : nat) (h1 : term18) : term76 n.
Proof. exact (fun h0 : term77 n => @lem200521 n h1). Qed.
Lemma lem200524 (p : Prop) : (term78 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem200525 (n : nat) : (term76 n) = ((term40 n) = n).
Proof. exact (@lem200524 ((term40 n) = n)). Qed.
Lemma lem200526 (n : nat) (h1 : term18) : (term40 n) = n.
Proof. exact (EQ_MP (@lem200525 n) (@lem200522 n h1)). Qed.
Lemma lem200528 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem200529 (n : nat) : (term40 n) = (term40 n).
Proof. exact (@lem200528 (term40 n)). Qed.
Lemma lem200530 (n : nat) : term79 n.
Proof. exact (fun h0 : term80 n => @lem200529 n). Qed.
Lemma lem200532 (p : Prop) : (term78 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem200533 (n : nat) : (term79 n) = ((term40 n) = (term40 n)).
Proof. exact (@lem200532 ((term40 n) = (term40 n))). Qed.
Lemma lem200534 (n : nat) : (term40 n) = (term40 n).
Proof. exact (EQ_MP (@lem200533 n) (@lem200530 n)). Qed.
Lemma lem200552 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem200553 (y : nat) (x : nat) (z : nat) : (term81 x y z) = (term82 y x z).
Proof. exact (@lem200552 (y = z) (term83 x z)). Qed.
Lemma lem200563 (x : nat) (y : nat) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem200564 (y : nat) (x : nat) (z : nat) : (term75 x y z) = (term85 y x z).
Proof. exact (MK_COMB (@lem200563 x y) (@lem200553 y x z)). Qed.
Lemma lem200568 (q : Prop) (p : Prop) (r : Prop) : (term86 p q r) = (term86 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem200569 (y : nat) (x : nat) (z : nat) : (term85 y x z) = (term87 y x z).
Proof. exact (@lem200568 (y = z) (term83 x y) (term83 x z)). Qed.
Lemma lem200591 (y : nat) (x : nat) (z : nat) : (term75 x y z) = (term87 y x z).
Proof. exact (TRANS (@lem200564 y x z) (@lem200569 y x z)). Qed.
Lemma lem200592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem200593 (y : nat) (x : nat) (z : nat) : (term88 x y z) = (term89 y x z).
Proof. exact (MK_COMB (@lem200592) (@lem200591 y x z)). Qed.
Lemma lem200615 (y : nat) (x : nat) (z : nat) : (term87 y x z) = (term87 y x z).
Proof. exact (eq_refl (term87 y x z)). Qed.
Lemma lem200616 (y : nat) (x : nat) (z : nat) : ((term75 x y z) = (term87 y x z)) = ((term87 y x z) = (term87 y x z)).
Proof. exact (MK_COMB (@lem200593 y x z) (@lem200615 y x z)). Qed.
Lemma lem200618 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem200619 (x : Prop) : (x = x) = True.
Proof. exact (@lem200618 Prop x). Qed.
Lemma lem200620 (y : nat) (x : nat) (z : nat) : ((term87 y x z) = (term87 y x z)) = True.
Proof. exact (@lem200619 (term87 y x z)). Qed.
Lemma lem200621 (y : nat) (x : nat) (z : nat) : ((term75 x y z) = (term87 y x z)) = True.
Proof. exact (TRANS (@lem200616 y x z) (@lem200620 y x z)). Qed.
Lemma lem200622 (y : nat) (x : nat) (z : nat) : True = ((term75 x y z) = (term87 y x z)).
Proof. exact (SYM (@lem200621 y x z)). Qed.
Lemma lem200623 (y : nat) (x : nat) (z : nat) : (term75 x y z) = (term87 y x z).
Proof. exact (EQ_MP (@lem200622 y x z) (@lem0)). Qed.
Lemma lem200624 (y : nat) (x : nat) (z : nat) : term87 y x z.
Proof. exact (EQ_MP (@lem200623 y x z) (@lem200518 x y z)). Qed.
Lemma lem200626 (b : Prop) (a : Prop) : (a \/ b) = (term90 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem200627 (x : nat) (y : nat) (z : nat) : (term87 y x z) = (term91 x y z).
Proof. exact (@lem200626 (term92 y x z) (y = z)). Qed.
Lemma lem200629 (a : Prop) (b : Prop) : (term93 a b) = (term94 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem200630 (y : nat) (x : nat) (z : nat) : (term95 y x z) = (term96 y x z).
Proof. exact (@lem200629 (term83 x y) (term83 x z)). Qed.
Lemma lem200632 (a : Prop) : (term97 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem200633 (x : nat) (y : nat) : (term98 x y) = (x = y).
Proof. exact (@lem200632 (x = y)). Qed.
Lemma lem200634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem200635 (x : nat) (y : nat) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem200634) (@lem200633 x y)). Qed.
Lemma lem200637 (a : Prop) : (term97 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem200638 (x : nat) (z : nat) : (term98 x z) = (x = z).
Proof. exact (@lem200637 (x = z)). Qed.
Lemma lem200639 (y : nat) (x : nat) (z : nat) : (term96 y x z) = (term101 y x z).
Proof. exact (MK_COMB (@lem200635 x y) (@lem200638 x z)). Qed.
Lemma lem200640 (y : nat) (x : nat) (z : nat) : (term95 y x z) = (term101 y x z).
Proof. exact (TRANS (@lem200630 y x z) (@lem200639 y x z)). Qed.
Lemma lem200641 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem200642 (y : nat) (x : nat) (z : nat) : (term102 y x z) = (term103 y x z).
Proof. exact (MK_COMB (@lem200641) (@lem200640 y x z)). Qed.
Lemma lem200643 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem200644 (x : nat) (y : nat) (z : nat) : (term91 x y z) = (term104 x y z).
Proof. exact (MK_COMB (@lem200642 y x z) (@lem200643 y z)). Qed.
Lemma lem200645 (x : nat) (y : nat) (z : nat) : (term87 y x z) = (term104 x y z).
Proof. exact (TRANS (@lem200627 x y z) (@lem200644 x y z)). Qed.
Lemma lem200647 (n : nat) (h1 : term18) : term105 n.
Proof. exact (conj (@lem200526 n h1) (@lem200534 n)). Qed.
Lemma lem200649 (x : nat) (y : nat) (z : nat) : term104 x y z.
Proof. exact (EQ_MP (@lem200645 x y z) (@lem200624 y x z)). Qed.
Lemma lem200650 (n : nat) : term106 n.
Proof. exact (@lem200649 (term40 n) n (term40 n)). Qed.
Lemma lem200653 (n : nat) (h1 : term18) : n = (term40 n).
Proof. exact (@lem200650 n (@lem200647 n h1)). Qed.
Lemma lem200654 (n : nat) (h1 : term18) : term107 n.
Proof. exact (fun h0 : term108 n => @lem200653 n h1). Qed.
Lemma lem200656 (p : Prop) : (term78 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem200657 (n : nat) : (term107 n) = (n = (term40 n)).
Proof. exact (@lem200656 (n = (term40 n))). Qed.
Lemma lem200658 (n : nat) (h1 : term18) : n = (term40 n).
Proof. exact (EQ_MP (@lem200657 n) (@lem200654 n h1)). Qed.
Lemma lem200661 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem200663 (_4027 : nat) (n : nat) : (term61 _4027 n) = (term109 _4027 n).
Proof. exact (@lem200661 (n = (Nat.mul _4027 n))). Qed.
Lemma lem200666 (_4027 : nat) (n : nat) (h1 : term64 n) : term109 _4027 n.
Proof. exact (EQ_MP (@lem200663 _4027 n) (@lem200450 _4027 n h1)). Qed.
Lemma lem200667 (n : nat) (h1 : term64 n) : term110 n.
Proof. exact (@lem200666 term111 n h1). Qed.
Lemma lem200670 (n : nat) (h1 : term64 n) (h2 : term18) : False.
Proof. exact (@lem200667 n h1 (@lem200658 n h2)). Qed.
Lemma lem200671 (n : nat) (h1 : term64 n) (h2 : term18) : term112.
Proof. exact (fun h0 : ~ False => @lem200670 n h1 h2). Qed.
Lemma lem200673 (p : Prop) : (term78 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem200674 : term112 = False.
Proof. exact (@lem200673 False). Qed.
Lemma lem200675 (n : nat) (h1 : term64 n) (h2 : term18) : False.
Proof. exact (EQ_MP (@lem200674) (@lem200671 n h1 h2)). Qed.
Lemma lem200676 (n : nat) (h1 : term64 n) (h2 : term18) : (term64 n) = False.
Proof. exact (prop_ext (fun h3 : term64 n => @lem200675 n h1 h2) (fun h3 : False => @lem200373 n h1)). Qed.
Lemma lem200677 (n : nat) (h1 : term64 n) (h2 : term18) : False.
Proof. exact (EQ_MP (@lem200676 n h1 h2) (@lem200373 n h1)). Qed.
Lemma lem200678 (n : nat) (h1 : term64 n) (h2 : term18) : (term64 n) = False.
Proof. exact (prop_ext (fun h3 : term64 n => @lem200677 n h1 h2) (fun h3 : False => @lem200356 n h1)). Qed.
Lemma lem200679 (n : nat) (h1 : term64 n) (h2 : term18) : False.
Proof. exact (EQ_MP (@lem200678 n h1 h2) (@lem200356 n h1)). Qed.
Lemma lem200680 (n : nat) (h1 : term64 n) (h2 : term18) : term18 = False.
Proof. exact (prop_ext (fun h3 : term18 => @lem200679 n h1 h2) (fun h3 : False => @lem200341 h2)). Qed.
Lemma lem200681 (n : nat) (h1 : term64 n) (h2 : term18) : False.
Proof. exact (EQ_MP (@lem200680 n h1 h2) (@lem200341 h2)). Qed.
Lemma lem200682 (h1 : term11) (h2 : term18) : False.
Proof. exact (ex_elim (@lem200128 h1) (fun n : nat => fun h0 : term71 n => @lem200681 n h0 h2)). Qed.
Lemma lem200683 (h1 : term11) (h2 : term18) : term18 = False.
Proof. exact (prop_ext (fun h3 : term18 => @lem200682 h1 h2) (fun h3 : False => @lem200210 h2)). Qed.
Lemma lem200684 (h1 : term11) (h2 : term18) : False.
Proof. exact (EQ_MP (@lem200683 h1 h2) (@lem200210 h2)). Qed.
Lemma lem200685 (h1 : term11) : term16.
Proof. exact (fun h0 : term18 => @lem200684 h1 h0). Qed.
Lemma lem200686 : term16 = term17.
Proof. exact (@lem69 term18). Qed.
Lemma lem200687 (h1 : term11) : term17.
Proof. exact (EQ_MP (@lem200686) (@lem200685 h1)). Qed.
Lemma lem200688 : term20.
Proof. exact (fun h0 : term11 => @lem200687 h0). Qed.
Lemma lem200689 : term12.
Proof. exact (EQ_MP (@lem200092) (@lem200688)). Qed.
Lemma lem200691 : term12.
Proof. exact (@lem199894 (@lem200689)). Qed.
Lemma lem200692 (h1 : term11) : term16.
Proof. exact (@lem200691 (@lem199879 h1)). Qed.
Lemma lem200693 (h1 : term11) : False.
Proof. exact (@lem200692 h1 (@lem81645)). Qed.
Lemma lem200694 (h1 : term11) : term11 = False.
Proof. exact (prop_ext (fun h2 : term11 => @lem200693 h1) (fun h2 : False => @lem199879 h1)). Qed.
Lemma lem200695 (h1 : term11) : False.
Proof. exact (EQ_MP (@lem200694 h1) (@lem199879 h1)). Qed.
Lemma lem200696 : term10.
Proof. exact (fun h0 : term11 => @lem200695 h0). Qed.
Lemma lem200697 : term8.
Proof. exact (EQ_MP (@lem199878) (@lem200696)). Qed.
Lemma lem200698 : term7.
Proof. exact (EQ_MP (@lem199874) (@lem200697)). Qed.
