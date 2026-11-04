object StreamEqual {
  def streamequal[A](a:Any,b:Any): Boolean = a==b
}

object def_automaton_Event_scalaExec {

trait below[A] {
  val `def_automaton_Event_scalaExec.below`: (A, A) => Boolean
}
def below[A](a: A, b: A)(implicit A: below[A]): Boolean =
  A.`def_automaton_Event_scalaExec.below`(a, b)
object below{
  implicit def
    `def_automaton_Event_scalaExec.below_sbelem`[A : chan : equal]:
      below[sbelem[A]]
    = new below[sbelem[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: sbelem[A], b: sbelem[A]) =>
      below_sbelema[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.below_stream`[A : countable : equal]:
      below[stream[A]]
    = new below[stream[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: stream[A], b: stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.below_sb`[A : chan : enum]: below[sb[A]] =
    new below[sb[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: sb[A], b: sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

trait countable[A] {
}
object countable{
  implicit def
    `def_automaton_Event_scalaExec.countable_eventwithchan`[A : chan : countable]:
      countable[eventwithchan[A]]
    = new countable[eventwithchan[A]] {
  }
  implicit def
    `def_automaton_Event_scalaExec.countable_tstimed`[A : countable : one_chan]:
      countable[tstimed[A]]
    = new countable[tstimed[A]] {
  }
  implicit def
    `def_automaton_Event_scalaExec.countable_channelsa`: countable[channelsa] =
    new countable[channelsa] {
  }
  implicit def
    `def_automaton_Event_scalaExec.countable_channels`: countable[channels] =
    new countable[channels] {
  }
  implicit def
    `def_automaton_Event_scalaExec.countable_event`[A : countable]:
      countable[event[A]]
    = new countable[event[A]] {
  }
  implicit def
    `def_automaton_Event_scalaExec.countable_prod`[A : countable,
            B : countable]:
      countable[(A, B)]
    = new countable[(A, B)] {
  }
  implicit def
    `def_automaton_Event_scalaExec.countable_m_pure`: countable[M_pure] = new
    countable[M_pure] {
  }
  implicit def
    `def_automaton_Event_scalaExec.countable_list`[A : countable]:
      countable[List[A]]
    = new countable[List[A]] {
  }
  implicit def `def_automaton_Event_scalaExec.countable_m`: countable[M] = new
    countable[M] {
  }
  implicit def
    `def_automaton_Event_scalaExec.countable_bool`: countable[Boolean] = new
    countable[Boolean] {
  }
}

trait finite[A] extends countable[A] {
}
object finite{
  implicit def
    `def_automaton_Event_scalaExec.finite_tstimed`[A : finite : one_chan]:
      finite[tstimed[A]]
    = new finite[tstimed[A]] {
  }
  implicit def
    `def_automaton_Event_scalaExec.finite_channelsa`: finite[channelsa] = new
    finite[channelsa] {
  }
  implicit def `def_automaton_Event_scalaExec.finite_channels`: finite[channels]
    = new finite[channels] {
  }
}

trait enum[A] extends finite[A] {
  val `def_automaton_Event_scalaExec.enum`: List[A]
  val `def_automaton_Event_scalaExec.enum_all`: (A => Boolean) => Boolean
  val `def_automaton_Event_scalaExec.enum_ex`: (A => Boolean) => Boolean
}
def enum[A](implicit A: enum[A]): List[A] =
  A.`def_automaton_Event_scalaExec.enum`
def enum_all[A](a: A => Boolean)(implicit A: enum[A]): Boolean =
  A.`def_automaton_Event_scalaExec.enum_all`(a)
def enum_ex[A](a: A => Boolean)(implicit A: enum[A]): Boolean =
  A.`def_automaton_Event_scalaExec.enum_ex`(a)
object enum{
  implicit def
    `def_automaton_Event_scalaExec.enum_tstimed`[A : enum : one_chan]:
      enum[tstimed[A]]
    = new enum[tstimed[A]] {
    val `def_automaton_Event_scalaExec.enum` = enum_tstimeda[A]
    val `def_automaton_Event_scalaExec.enum_all` = (a: (tstimed[A]) => Boolean)
      => enum_all_tstimed[A](a)
    val `def_automaton_Event_scalaExec.enum_ex` = (a: (tstimed[A]) => Boolean)
      => enum_ex_tstimed[A](a)
  }
  implicit def `def_automaton_Event_scalaExec.enum_channelsa`: enum[channelsa] =
    new enum[channelsa] {
    val `def_automaton_Event_scalaExec.enum` = enum_channelsc
    val `def_automaton_Event_scalaExec.enum_all` = (a: channelsa => Boolean) =>
      enum_all_channelsa(a)
    val `def_automaton_Event_scalaExec.enum_ex` = (a: channelsa => Boolean) =>
      enum_ex_channelsa(a)
  }
  implicit def `def_automaton_Event_scalaExec.enum_channels`: enum[channels] =
    new enum[channels] {
    val `def_automaton_Event_scalaExec.enum` = enum_channelsb
    val `def_automaton_Event_scalaExec.enum_all` = (a: channels => Boolean) =>
      enum_all_channels(a)
    val `def_automaton_Event_scalaExec.enum_ex` = (a: channels => Boolean) =>
      enum_ex_channels(a)
  }
}

def All[A : enum](p: A => Boolean): Boolean = enum_all[A](p)

def below_fun[A : enum, B : below]: (A => B) => (A => B) => Boolean =
  ((f: A => B) => (g: A => B) => All[A](((x: A) => below[B](f(x), g(x)))))

abstract sealed class stream[A]
final case class stream_bottom_nc[A]() extends stream[A]
final case class lscons_u_nc[A](a: A, b: stream[A]) extends stream[A]

abstract sealed class char
final case class Chara(a: Boolean, b: Boolean, c: Boolean, d: Boolean,
                        e: Boolean, f: Boolean, g: Boolean, h: Boolean)
  extends char

abstract sealed class nat
final case class zero_nat() extends nat
final case class Suc(a: nat) extends nat

abstract sealed class M_pure
final case class booleventconstr(a: Boolean) extends M_pure
final case class boolsyncconstr(a: Boolean) extends M_pure
final case class nateventconstr(a: nat) extends M_pure
final case class natsyncconstr(a: nat) extends M_pure
final case class stringeventconstr(a: List[char]) extends M_pure
final case class stringsyncconstr(a: List[char]) extends M_pure

abstract sealed class event[A]
final case class Eventa[A](a: A) extends event[A]
final case class Tick[A]() extends event[A]

abstract sealed class tsyn[A]
final case class Msg[A](a: A) extends tsyn[A]
final case class eps[A]() extends tsyn[A]

abstract sealed class M_timed
final case class Tsyna(a: tsyn[M_pure]) extends M_timed
final case class Tone(a: M_pure) extends M_timed
final case class Tlive(a: event[M_pure]) extends M_timed
final case class Tfin(a: List[M_pure]) extends M_timed

abstract sealed class M
final case class Untimed(a: M_pure) extends M
final case class Timed(a: M_timed) extends M

abstract sealed class msgtype
final case class Tboolevent() extends msgtype
final case class Tboolsync() extends msgtype
final case class Tnatevent() extends msgtype
final case class Tnatsync() extends msgtype
final case class Tstringevent() extends msgtype
final case class Tstringsync() extends msgtype
final case class Tnone() extends msgtype

abstract sealed class timetype
final case class Tuntimed() extends timetype
final case class Ttone() extends timetype
final case class Ttfin() extends timetype
final case class Ttlive() extends timetype
final case class Ttsyn() extends timetype

abstract sealed class channel
final case class CH(a: List[char], b: timetype, c: msgtype) extends channel

abstract sealed class myself[A]
final case class DUMMY[A]() extends myself[A]

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

trait rep[A] {
  val `def_automaton_Event_scalaExec.Rep`: A => channel
  val `def_automaton_Event_scalaExec.Abs`: channel => A
  val `def_automaton_Event_scalaExec.chandom`: (myself[A]) => set[channel]
}
def Rep[A](a: A)(implicit A: rep[A]): channel =
  A.`def_automaton_Event_scalaExec.Rep`(a)
def Abs[A](a: channel)(implicit A: rep[A]): A =
  A.`def_automaton_Event_scalaExec.Abs`(a)
def chandom[A](a: myself[A])(implicit A: rep[A]): set[channel] =
  A.`def_automaton_Event_scalaExec.chandom`(a)
object rep{
  implicit def
    `def_automaton_Event_scalaExec.rep_tstimed`[A : enum : one_chan]:
      rep[tstimed[A]]
    = new rep[tstimed[A]] {
    val `def_automaton_Event_scalaExec.Rep` = (a: tstimed[A]) =>
      Rep_tstimeda[A](a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_tstimed[A](a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[tstimed[A]]) =>
      chandom_tstimed[A](a)
  }
  implicit def `def_automaton_Event_scalaExec.rep_channelsa`: rep[channelsa] =
    new rep[channelsa] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channelsa) => Rep_channelsc(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channelsa(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `def_automaton_Event_scalaExec.rep_channels`: rep[channels] = new
    rep[channels] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channels) => Rep_channelsb(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channels(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channels]) =>
      chandom_channels(a)
  }
}

trait chan[A] extends rep[A] {
}
object chan{
  implicit def
    `def_automaton_Event_scalaExec.chan_tstimed`[A : enum : one_chan]:
      chan[tstimed[A]]
    = new chan[tstimed[A]] {
    val `def_automaton_Event_scalaExec.Rep` = (a: tstimed[A]) =>
      Rep_tstimeda[A](a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_tstimed[A](a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[tstimed[A]]) =>
      chandom_tstimed[A](a)
  }
  implicit def `def_automaton_Event_scalaExec.chan_channelsa`: chan[channelsa] =
    new chan[channelsa] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channelsa) => Rep_channelsc(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channelsa(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `def_automaton_Event_scalaExec.chan_channels`: chan[channels] =
    new chan[channels] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channels) => Rep_channelsb(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channels(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channels]) =>
      chandom_channels(a)
  }
}

abstract sealed class sb[A]
final case class Abs_sb[A](a: A => stream[M]) extends sb[A]

def Rep_sb[A : chan](x0: sb[A]): A => stream[M] = x0 match {
  case Abs_sb(x) => x
}

trait equal[A] {
  val `def_automaton_Event_scalaExec.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean =
  A.`def_automaton_Event_scalaExec.equal`(a, b)
object equal{
  implicit def
    `def_automaton_Event_scalaExec.equal_eventwithchan`[A : chan]:
      equal[eventwithchan[A]]
    = new equal[eventwithchan[A]] {
    val `def_automaton_Event_scalaExec.equal` =
      (a: eventwithchan[A], b: eventwithchan[A]) =>
      equal_eventwithchana[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.equal_tstimed`[A : equal : one_chan]:
      equal[tstimed[A]]
    = new equal[tstimed[A]] {
    val `def_automaton_Event_scalaExec.equal` = (a: tstimed[A], b: tstimed[A])
      => equal_tstimeda[A](a, b)
  }
  implicit def `def_automaton_Event_scalaExec.equal_channelsa`: equal[channelsa]
    = new equal[channelsa] {
    val `def_automaton_Event_scalaExec.equal` = (a: channelsa, b: channelsa) =>
      equal_channelsc(a, b)
  }
  implicit def `def_automaton_Event_scalaExec.equal_channels`: equal[channels] =
    new equal[channels] {
    val `def_automaton_Event_scalaExec.equal` = (a: channels, b: channels) =>
      equal_channelsb(a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.equal_event`[A : equal]: equal[event[A]] =
    new equal[event[A]] {
    val `def_automaton_Event_scalaExec.equal` = (a: event[A], b: event[A]) =>
      equal_eventa[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.equal_prod`[A : equal, B : equal]:
      equal[(A, B)]
    = new equal[(A, B)] {
    val `def_automaton_Event_scalaExec.equal` = (a: (A, B), b: (A, B)) =>
      equal_proda[A, B](a, b)
  }
  implicit def `def_automaton_Event_scalaExec.equal_channel`: equal[channel] =
    new equal[channel] {
    val `def_automaton_Event_scalaExec.equal` = (a: channel, b: channel) =>
      equal_channela(a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.equal_sbelem`[A : chan : equal]:
      equal[sbelem[A]]
    = new equal[sbelem[A]] {
    val `def_automaton_Event_scalaExec.equal` = (a: sbelem[A], b: sbelem[A]) =>
      equal_sbelema[A](a, b)
  }
  implicit def `def_automaton_Event_scalaExec.equal_m_pure`: equal[M_pure] = new
    equal[M_pure] {
    val `def_automaton_Event_scalaExec.equal` = (a: M_pure, b: M_pure) =>
      equal_m_purea(a, b)
  }
  implicit def `def_automaton_Event_scalaExec.equal_char`: equal[char] = new
    equal[char] {
    val `def_automaton_Event_scalaExec.equal` = (a: char, b: char) =>
      equal_chara(a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.equal_list`[A : equal]: equal[List[A]] = new
    equal[List[A]] {
    val `def_automaton_Event_scalaExec.equal` = (a: List[A], b: List[A]) =>
      equal_lista[A](a, b)
  }
  implicit def `def_automaton_Event_scalaExec.equal_m`: equal[M] = new equal[M]
    {
    val `def_automaton_Event_scalaExec.equal` = (a: M, b: M) => equal_ma(a, b)
  }
  implicit def `def_automaton_Event_scalaExec.equal_bool`: equal[Boolean] = new
    equal[Boolean] {
    val `def_automaton_Event_scalaExec.equal` = (a: Boolean, b: Boolean) =>
      equal_boola(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

def below_streama[A : countable : equal](x0: stream[A], as: stream[A]): Boolean
  =
  (x0, as) match {
  case (lscons_u_nc(a, as), lscons_u_nc(b, bs)) =>
    (if (! (eq[A](a, b))) false else below_streama[A](as, bs))
  case (stream_bottom_nc(), as) => true
}

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

def equal_lista[A : equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) => eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

def equal_nat(x0: nat, x1: nat): Boolean = (x0, x1) match {
  case (zero_nat(), Suc(x2)) => false
  case (Suc(x2), zero_nat()) => false
  case (Suc(x2), Suc(y2)) => equal_nat(x2, y2)
  case (zero_nat(), zero_nat()) => true
}

def equal_chara(x0: char, x1: char): Boolean = (x0, x1) match {
  case (Chara(x1, x2, x3, x4, x5, x6, x7, x8),
         Chara(y1, y2, y3, y4, y5, y6, y7, y8))
    => equal_boola(x1, y1) &&
         (equal_boola(x2, y2) &&
           (equal_boola(x3, y3) &&
             (equal_boola(x4, y4) &&
               (equal_boola(x5, y5) &&
                 (equal_boola(x6, y6) &&
                   (equal_boola(x7, y7) && equal_boola(x8, y8)))))))
}

def equal_m_purea(x0: M_pure, x1: M_pure): Boolean = (x0, x1) match {
  case (stringeventconstr(x5), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), stringeventconstr(x5)) => false
  case (natsyncconstr(x4), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), natsyncconstr(x4)) => false
  case (natsyncconstr(x4), stringeventconstr(x5)) => false
  case (stringeventconstr(x5), natsyncconstr(x4)) => false
  case (nateventconstr(x3), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), nateventconstr(x3)) => false
  case (nateventconstr(x3), stringeventconstr(x5)) => false
  case (stringeventconstr(x5), nateventconstr(x3)) => false
  case (nateventconstr(x3), natsyncconstr(x4)) => false
  case (natsyncconstr(x4), nateventconstr(x3)) => false
  case (boolsyncconstr(x2), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), boolsyncconstr(x2)) => false
  case (boolsyncconstr(x2), stringeventconstr(x5)) => false
  case (stringeventconstr(x5), boolsyncconstr(x2)) => false
  case (boolsyncconstr(x2), natsyncconstr(x4)) => false
  case (natsyncconstr(x4), boolsyncconstr(x2)) => false
  case (boolsyncconstr(x2), nateventconstr(x3)) => false
  case (nateventconstr(x3), boolsyncconstr(x2)) => false
  case (booleventconstr(x1), stringsyncconstr(x6)) => false
  case (stringsyncconstr(x6), booleventconstr(x1)) => false
  case (booleventconstr(x1), stringeventconstr(x5)) => false
  case (stringeventconstr(x5), booleventconstr(x1)) => false
  case (booleventconstr(x1), natsyncconstr(x4)) => false
  case (natsyncconstr(x4), booleventconstr(x1)) => false
  case (booleventconstr(x1), nateventconstr(x3)) => false
  case (nateventconstr(x3), booleventconstr(x1)) => false
  case (booleventconstr(x1), boolsyncconstr(x2)) => false
  case (boolsyncconstr(x2), booleventconstr(x1)) => false
  case (stringsyncconstr(x6), stringsyncconstr(y6)) => equal_lista[char](x6, y6)
  case (stringeventconstr(x5), stringeventconstr(y5)) =>
    equal_lista[char](x5, y5)
  case (natsyncconstr(x4), natsyncconstr(y4)) => equal_nat(x4, y4)
  case (nateventconstr(x3), nateventconstr(y3)) => equal_nat(x3, y3)
  case (boolsyncconstr(x2), boolsyncconstr(y2)) => equal_boola(x2, y2)
  case (booleventconstr(x1), booleventconstr(y1)) => equal_boola(x1, y1)
}

def equal_eventa[A : equal](x0: event[A], x1: event[A]): Boolean = (x0, x1)
  match {
  case (Eventa(x1), Tick()) => false
  case (Tick(), Eventa(x1)) => false
  case (Eventa(x1), Eventa(y1)) => eq[A](x1, y1)
  case (Tick(), Tick()) => true
}

def equal_tsyn[A : equal](x0: tsyn[A], x1: tsyn[A]): Boolean = (x0, x1) match {
  case (Msg(x1), eps()) => false
  case (eps(), Msg(x1)) => false
  case (Msg(x1), Msg(y1)) => eq[A](x1, y1)
  case (eps(), eps()) => true
}

def equal_m_timed(x0: M_timed, x1: M_timed): Boolean = (x0, x1) match {
  case (Tlive(x3), Tfin(x4)) => false
  case (Tfin(x4), Tlive(x3)) => false
  case (Tone(x2), Tfin(x4)) => false
  case (Tfin(x4), Tone(x2)) => false
  case (Tone(x2), Tlive(x3)) => false
  case (Tlive(x3), Tone(x2)) => false
  case (Tsyna(x1), Tfin(x4)) => false
  case (Tfin(x4), Tsyna(x1)) => false
  case (Tsyna(x1), Tlive(x3)) => false
  case (Tlive(x3), Tsyna(x1)) => false
  case (Tsyna(x1), Tone(x2)) => false
  case (Tone(x2), Tsyna(x1)) => false
  case (Tfin(x4), Tfin(y4)) => equal_lista[M_pure](x4, y4)
  case (Tlive(x3), Tlive(y3)) => equal_eventa[M_pure](x3, y3)
  case (Tone(x2), Tone(y2)) => equal_m_purea(x2, y2)
  case (Tsyna(x1), Tsyna(y1)) => equal_tsyn[M_pure](x1, y1)
}

def equal_ma(x0: M, x1: M): Boolean = (x0, x1) match {
  case (Untimed(x1), Timed(x2)) => false
  case (Timed(x2), Untimed(x1)) => false
  case (Timed(x2), Timed(y2)) => equal_m_timed(x2, y2)
  case (Untimed(x1), Untimed(y1)) => equal_m_purea(x1, y1)
}

def below_sba[A : chan : enum]: (sb[A]) => (sb[A]) => Boolean =
  ((x: sb[A]) => (y: sb[A]) =>
    below_fun[A, stream[M]].apply(Rep_sb[A](x)).apply(Rep_sb[A](y)))

trait po[A] extends below[A] {
}
object po{
  implicit def
    `def_automaton_Event_scalaExec.po_sbelem`[A : chan : equal]: po[sbelem[A]] =
    new po[sbelem[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: sbelem[A], b: sbelem[A]) =>
      below_sbelema[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.po_stream`[A : countable : equal]:
      po[stream[A]]
    = new po[stream[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: stream[A], b: stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def `def_automaton_Event_scalaExec.po_sb`[A : chan : enum]: po[sb[A]]
    = new po[sb[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: sb[A], b: sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

trait cpo[A] extends po[A] {
}
object cpo{
  implicit def
    `def_automaton_Event_scalaExec.cpo_sbelem`[A : chan : equal]: cpo[sbelem[A]]
    = new cpo[sbelem[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: sbelem[A], b: sbelem[A]) =>
      below_sbelema[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.cpo_stream`[A : countable : equal]:
      cpo[stream[A]]
    = new cpo[stream[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: stream[A], b: stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.cpo_sb`[A : chan : enum]: cpo[sb[A]] = new
    cpo[sb[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: sb[A], b: sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

trait pcpo[A] extends cpo[A] {
}
object pcpo{
  implicit def
    `def_automaton_Event_scalaExec.pcpo_stream`[A : countable : equal]:
      pcpo[stream[A]]
    = new pcpo[stream[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: stream[A], b: stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.pcpo_sb`[A : chan : enum]: pcpo[sb[A]] = new
    pcpo[sb[A]] {
    val `def_automaton_Event_scalaExec.below` = (a: sb[A], b: sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

def sconc_nc[A : countable](s1: stream[A], s2: stream[A]): stream[A] = (s1, s2)
  match {
  case (lscons_u_nc(a, s1), s2) => lscons_u_nc[A](a, sconc_nc[A](s1, s2))
  case (stream_bottom_nc(), s2) => s2
  case (s1, stream_bottom_nc()) => s1
}

def sbconc_nc[A : chan](sb1: sb[A], sb2: sb[A]): sb[A] =
  Abs_sb[A](((c: A) =>
              sconc_nc[M]((Rep_sb[A](sb1)).apply(c),
                           (Rep_sb[A](sb2)).apply(c))))

abstract sealed class cfun[B, A]
final case class Abs_cfun[B, A](a: B => A) extends cfun[B, A]

def conc_sba[A : chan : enum](sb: sb[A]): cfun[sb[A], sb[A]] =
  Abs_cfun[sb[A], sb[A]](((a: sb[A]) => sbconc_nc[A](sb, a)))

trait conc[A] extends pcpo[A] {
  val `def_automaton_Event_scalaExec.conc`: A => cfun[A, A]
}
def conc[A](a: A)(implicit A: conc[A]): cfun[A, A] =
  A.`def_automaton_Event_scalaExec.conc`(a)
object conc{
  implicit def
    `def_automaton_Event_scalaExec.conc_stream`[A : countable : equal]:
      conc[stream[A]]
    = new conc[stream[A]] {
    val `def_automaton_Event_scalaExec.conc` = (a: stream[A]) =>
      conc_streama[A](a)
    val `def_automaton_Event_scalaExec.below` = (a: stream[A], b: stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.conc_sb`[A : chan : enum]: conc[sb[A]] = new
    conc[sb[A]] {
    val `def_automaton_Event_scalaExec.conc` = (a: sb[A]) => conc_sba[A](a)
    val `def_automaton_Event_scalaExec.below` = (a: sb[A], b: sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

def bot_nc_streama[A : countable]: stream[A] = stream_bottom_nc[A]()

def bot_nc_sba[A : chan]: sb[A] = Abs_sb[A](((_: A) => bot_nc_streama[M]))

trait bot_nc[A] extends pcpo[A] {
  val `def_automaton_Event_scalaExec.bot_nc`: A
}
def bot_nc[A](implicit A: bot_nc[A]): A =
  A.`def_automaton_Event_scalaExec.bot_nc`
object bot_nc{
  implicit def
    `def_automaton_Event_scalaExec.bot_nc_stream`[A : countable : equal]:
      bot_nc[stream[A]]
    = new bot_nc[stream[A]] {
    val `def_automaton_Event_scalaExec.bot_nc` = bot_nc_streama[A]
    val `def_automaton_Event_scalaExec.below` = (a: stream[A], b: stream[A]) =>
      below_streama[A](a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.bot_nc_sb`[A : chan : enum]: bot_nc[sb[A]] =
    new bot_nc[sb[A]] {
    val `def_automaton_Event_scalaExec.bot_nc` = bot_nc_sba[A]
    val `def_automaton_Event_scalaExec.below` = (a: sb[A], b: sb[A]) =>
      below_sba[A].apply(a).apply(b)
  }
}

def conc_streama[A : countable : equal](s1: stream[A]):
      cfun[stream[A], stream[A]]
  =
  Abs_cfun[stream[A], stream[A]](((a: stream[A]) => sconc_nc[A](s1, a)))

abstract sealed class sbelem[A]
final case class Abs_sbelem[A](a: Option[A => M]) extends sbelem[A]

def equal_sbelema[A : chan : equal](a: sbelem[A], b: sbelem[A]): Boolean =
  equal_sbelema[A](a, b)

def below_sbelema[A : chan : equal](sbe1: sbelem[A], sbe2: sbelem[A]): Boolean =
  eq[sbelem[A]](sbe1, sbe2)

def equal_timetype(x0: timetype, x1: timetype): Boolean = (x0, x1) match {
  case (Ttlive(), Ttsyn()) => false
  case (Ttsyn(), Ttlive()) => false
  case (Ttfin(), Ttsyn()) => false
  case (Ttsyn(), Ttfin()) => false
  case (Ttfin(), Ttlive()) => false
  case (Ttlive(), Ttfin()) => false
  case (Ttone(), Ttsyn()) => false
  case (Ttsyn(), Ttone()) => false
  case (Ttone(), Ttlive()) => false
  case (Ttlive(), Ttone()) => false
  case (Ttone(), Ttfin()) => false
  case (Ttfin(), Ttone()) => false
  case (Tuntimed(), Ttsyn()) => false
  case (Ttsyn(), Tuntimed()) => false
  case (Tuntimed(), Ttlive()) => false
  case (Ttlive(), Tuntimed()) => false
  case (Tuntimed(), Ttfin()) => false
  case (Ttfin(), Tuntimed()) => false
  case (Tuntimed(), Ttone()) => false
  case (Ttone(), Tuntimed()) => false
  case (Ttsyn(), Ttsyn()) => true
  case (Ttlive(), Ttlive()) => true
  case (Ttfin(), Ttfin()) => true
  case (Ttone(), Ttone()) => true
  case (Tuntimed(), Tuntimed()) => true
}

def equal_msgtype(x0: msgtype, x1: msgtype): Boolean = (x0, x1) match {
  case (Tstringsync(), Tnone()) => false
  case (Tnone(), Tstringsync()) => false
  case (Tstringevent(), Tnone()) => false
  case (Tnone(), Tstringevent()) => false
  case (Tstringevent(), Tstringsync()) => false
  case (Tstringsync(), Tstringevent()) => false
  case (Tnatsync(), Tnone()) => false
  case (Tnone(), Tnatsync()) => false
  case (Tnatsync(), Tstringsync()) => false
  case (Tstringsync(), Tnatsync()) => false
  case (Tnatsync(), Tstringevent()) => false
  case (Tstringevent(), Tnatsync()) => false
  case (Tnatevent(), Tnone()) => false
  case (Tnone(), Tnatevent()) => false
  case (Tnatevent(), Tstringsync()) => false
  case (Tstringsync(), Tnatevent()) => false
  case (Tnatevent(), Tstringevent()) => false
  case (Tstringevent(), Tnatevent()) => false
  case (Tnatevent(), Tnatsync()) => false
  case (Tnatsync(), Tnatevent()) => false
  case (Tboolsync(), Tnone()) => false
  case (Tnone(), Tboolsync()) => false
  case (Tboolsync(), Tstringsync()) => false
  case (Tstringsync(), Tboolsync()) => false
  case (Tboolsync(), Tstringevent()) => false
  case (Tstringevent(), Tboolsync()) => false
  case (Tboolsync(), Tnatsync()) => false
  case (Tnatsync(), Tboolsync()) => false
  case (Tboolsync(), Tnatevent()) => false
  case (Tnatevent(), Tboolsync()) => false
  case (Tboolevent(), Tnone()) => false
  case (Tnone(), Tboolevent()) => false
  case (Tboolevent(), Tstringsync()) => false
  case (Tstringsync(), Tboolevent()) => false
  case (Tboolevent(), Tstringevent()) => false
  case (Tstringevent(), Tboolevent()) => false
  case (Tboolevent(), Tnatsync()) => false
  case (Tnatsync(), Tboolevent()) => false
  case (Tboolevent(), Tnatevent()) => false
  case (Tnatevent(), Tboolevent()) => false
  case (Tboolevent(), Tboolsync()) => false
  case (Tboolsync(), Tboolevent()) => false
  case (Tnone(), Tnone()) => true
  case (Tstringsync(), Tstringsync()) => true
  case (Tstringevent(), Tstringevent()) => true
  case (Tnatsync(), Tnatsync()) => true
  case (Tnatevent(), Tnatevent()) => true
  case (Tboolsync(), Tboolsync()) => true
  case (Tboolevent(), Tboolevent()) => true
}

def equal_channela(x0: channel, x1: channel): Boolean = (x0, x1) match {
  case (CH(x1, x2, x3), CH(y1, y2, y3)) =>
    equal_lista[char](x1, y1) &&
      (equal_timetype(x2, y2) && equal_msgtype(x3, y3))
}

def equal_proda[A : equal, B : equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

abstract sealed class typerepa
final case class Typerepb(a: String, b: List[typerepa]) extends typerepa

abstract sealed class Substate
final case class state_s() extends Substate
final case class state_t() extends Substate

abstract sealed class State
final case class Stateconstr(a: Substate) extends State

abstract sealed class itself[A]
final case class typea[A]() extends itself[A]

def typerep_statea(t: itself[State]): typerepa =
  Typerepb("Event_States.State", Nil)

trait typerep[A] {
  val `def_automaton_Event_scalaExec.typerep`: (itself[A]) => typerepa
}
def typerep[A](a: itself[A])(implicit A: typerep[A]): typerepa =
  A.`def_automaton_Event_scalaExec.typerep`(a)
object typerep{
  implicit def `def_automaton_Event_scalaExec.typerep_state`: typerep[State] =
    new typerep[State] {
    val `def_automaton_Event_scalaExec.typerep` = (a: itself[State]) =>
      typerep_statea(a)
  }
}

abstract sealed class natural
final case class Nata(a: BigInt) extends natural

abstract sealed class num
final case class Onea() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

def one_natural: natural = Nata(BigInt(1))

def scomp[A, B, C, D](f: A => (B, C), g: B => C => D): A => D =
  ((x: A) => {
               val (a, b): (B, C) = f(x);
               (g(a))(b)
             })

def id[A]: A => A = ((x: A) => x)

def collapse[A, B](f: A => (A => (B, A), A)): A => (B, A) =
  scomp[A, A => (B, A), A, (B, A)](f, id[A => (B, A)])

abstract sealed class term
final case class Const(a: String, b: typerepa) extends term
final case class App(a: term, b: term) extends term
final case class Abs(a: String, b: typerepa, c: term) extends term
final case class Free(a: String, b: typerepa) extends term

trait zero[A] {
  val `def_automaton_Event_scalaExec.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`def_automaton_Event_scalaExec.zero`
object zero{
  implicit def `def_automaton_Event_scalaExec.zero_natural`: zero[natural] = new
    zero[natural] {
    val `def_automaton_Event_scalaExec.zero` = zero_naturala
  }
  implicit def `def_automaton_Event_scalaExec.zero_integer`: zero[BigInt] = new
    zero[BigInt] {
    val `def_automaton_Event_scalaExec.zero` = BigInt(0)
  }
}

trait plus[A] {
  val `def_automaton_Event_scalaExec.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A =
  A.`def_automaton_Event_scalaExec.plus`(a, b)
object plus{
  implicit def `def_automaton_Event_scalaExec.plus_natural`: plus[natural] = new
    plus[natural] {
    val `def_automaton_Event_scalaExec.plus` = (a: natural, b: natural) =>
      plus_naturala(a, b)
  }
  implicit def `def_automaton_Event_scalaExec.plus_integer`: plus[BigInt] = new
    plus[BigInt] {
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
  }
}

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => id[B]
  case (f, x :: xs) => comp[B, B, B](f(x), foldr[A, B](f, xs))
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add{
  implicit def
    `def_automaton_Event_scalaExec.semigroup_add_natural`:
      semigroup_add[natural]
    = new semigroup_add[natural] {
    val `def_automaton_Event_scalaExec.plus` = (a: natural, b: natural) =>
      plus_naturala(a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.semigroup_add_integer`: semigroup_add[BigInt]
    = new semigroup_add[BigInt] {
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add{
  implicit def
    `def_automaton_Event_scalaExec.monoid_add_natural`: monoid_add[natural] =
    new monoid_add[natural] {
    val `def_automaton_Event_scalaExec.zero` = zero_naturala
    val `def_automaton_Event_scalaExec.plus` = (a: natural, b: natural) =>
      plus_naturala(a, b)
  }
  implicit def
    `def_automaton_Event_scalaExec.monoid_add_integer`: monoid_add[BigInt] = new
    monoid_add[BigInt] {
    val `def_automaton_Event_scalaExec.zero` = BigInt(0)
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
  }
}

def sum_list[A : monoid_add](xs: List[A]): A =
  (foldr[A, A](((a: A) => (b: A) => plus[A](a, b)), xs)).apply(zero[A])

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (BigInt(0) < l)
           (if (BigInt(0) < k)
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k.abs /% l.abs)).apply(k).apply(l)
             else {
                    val (r, s): (BigInt, BigInt) =
                      ((k: BigInt) => (l: BigInt) => if (l == 0)
                        (BigInt(0), k) else (k.abs /% l.abs)).apply(k).apply(l);
                    (if (s == BigInt(0)) ((- r), BigInt(0))
                      else ((- r) - BigInt(1), l - s))
                  })
           else (if (l == BigInt(0)) (BigInt(0), k)
                  else apsnd[BigInt, BigInt,
                              BigInt](((a: BigInt) => (- a)),
                                       (if (k < BigInt(0))
 ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
   (k.abs /% l.abs)).apply(k).apply(l)
 else {
        val (r, s): (BigInt, BigInt) =
          ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
            (k.abs /% l.abs)).apply(k).apply(l);
        (if (s == BigInt(0)) ((- r), BigInt(0))
          else ((- r) - BigInt(1), (- l) - s))
      })))))

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def modulo_integer(k: BigInt, l: BigInt): BigInt =
  snd[BigInt, BigInt](divmod_integer(k, l))

def integer_of_natural(x0: natural): BigInt = x0 match {
  case Nata(x) => x
}

def modulo_natural(m: natural, n: natural): natural =
  Nata(modulo_integer(integer_of_natural(m), integer_of_natural(n)))

def times_natural(m: natural, n: natural): natural =
  Nata(integer_of_natural(m) * integer_of_natural(n))

def plus_naturala(m: natural, n: natural): natural =
  Nata(integer_of_natural(m) + integer_of_natural(n))

trait ord[A] {
  val `def_automaton_Event_scalaExec.less_eq`: (A, A) => Boolean
  val `def_automaton_Event_scalaExec.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`def_automaton_Event_scalaExec.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`def_automaton_Event_scalaExec.less`(a, b)
object ord{
  implicit def `def_automaton_Event_scalaExec.ord_integer`: ord[BigInt] = new
    ord[BigInt] {
    val `def_automaton_Event_scalaExec.less_eq` = (a: BigInt, b: BigInt) =>
      a <= b
    val `def_automaton_Event_scalaExec.less` = (a: BigInt, b: BigInt) => a < b
  }
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def natural_of_integer(k: BigInt): natural = Nata(max[BigInt](BigInt(0), k))

def minus_natural(m: natural, n: natural): natural =
  Nata(max[BigInt](BigInt(0), integer_of_natural(m) - integer_of_natural(n)))

def equal_natural(m: natural, n: natural): Boolean =
  integer_of_natural(m) == integer_of_natural(n)

def zero_naturala: natural = Nata(BigInt(0))

def iterate[A, B](k: natural, f: A => B => (A, B), x: A): B => (A, B) =
  (if (equal_natural(k, zero_naturala)) ((a: B) => (x, a))
    else scomp[B, A, B,
                (A, B)](f(x),
                         ((a: A) =>
                           iterate[A, B](minus_natural(k, one_natural), f, a))))

def divide_integer(k: BigInt, l: BigInt): BigInt =
  fst[BigInt, BigInt](divmod_integer(k, l))

def divide_natural(m: natural, n: natural): natural =
  Nata(divide_integer(integer_of_natural(m), integer_of_natural(n)))

def less_natural(m: natural, n: natural): Boolean =
  integer_of_natural(m) < integer_of_natural(n)

def minus_shift(r: natural, k: natural, l: natural): natural =
  (if (less_natural(k, l)) minus_natural(plus_naturala(r, k), l)
    else minus_natural(k, l))

def next(x0: (natural, natural)): (natural, (natural, natural)) = x0 match {
  case (v, w) =>
    {
      val k: natural = divide_natural(v, natural_of_integer(BigInt(53668)))
      val va: natural =
        minus_shift(natural_of_integer(BigInt(2147483563)),
                     times_natural(modulo_natural(v,
           natural_of_integer(BigInt(53668))),
                                    natural_of_integer(BigInt(40014))),
                     times_natural(k, natural_of_integer(BigInt(12211))))
      val l: natural = divide_natural(w, natural_of_integer(BigInt(52774)))
      val wa: natural =
        minus_shift(natural_of_integer(BigInt(2147483399)),
                     times_natural(modulo_natural(w,
           natural_of_integer(BigInt(52774))),
                                    natural_of_integer(BigInt(40692))),
                     times_natural(l, natural_of_integer(BigInt(3791))))
      val z: natural =
        plus_naturala(minus_shift(natural_of_integer(BigInt(2147483562)), va,
                                   plus_naturala(wa, one_natural)),
                       one_natural);
      (z, (va, wa))
    }
}

def less_eq_natural(m: natural, n: natural): Boolean =
  integer_of_natural(m) <= integer_of_natural(n)

def log(b: natural, i: natural): natural =
  (if (less_eq_natural(b, one_natural) || less_natural(i, b)) one_natural
    else plus_naturala(one_natural, log(b, divide_natural(i, b))))

def range(k: natural): ((natural, natural)) => (natural, (natural, natural)) =
  scomp[(natural, natural), natural, (natural, natural),
         (natural,
           (natural,
             natural))](iterate[natural,
                                 (natural,
                                   natural)](log(natural_of_integer(BigInt(2147483561)),
          k),
      ((l: natural) =>
        scomp[(natural, natural), natural, (natural, natural),
               (natural,
                 (natural,
                   natural))](((a: (natural, natural)) => next(a)),
                               ((v: natural) =>
                                 ((a: (natural, natural)) =>
                                   (plus_naturala(v,
           times_natural(l, natural_of_integer(BigInt(2147483561)))),
                                     a))))),
      one_natural),
                         ((v: natural) =>
                           ((a: (natural, natural)) =>
                             (modulo_natural(v, k), a))))

def pick[A](x0: List[(natural, A)], i: natural): A = (x0, i) match {
  case (x :: xs, i) =>
    (if (less_natural(i, fst[natural, A](x))) snd[natural, A](x)
      else pick[A](xs, minus_natural(i, fst[natural, A](x))))
}

def select_weight[A](xs: List[(natural, A)]):
      ((natural, natural)) => (A, (natural, natural))
  =
  scomp[(natural, natural), natural, (natural, natural),
         (A, (natural,
               natural))](range(sum_list[natural](map[(natural, A),
               natural](((a: (natural, A)) => fst[natural, A](a)), xs))),
                           ((k: natural) =>
                             ((a: (natural, natural)) => (pick[A](xs, k), a))))

def random_aux_substate(i: natural, j: natural, s: (natural, natural)):
      ((Substate, Unit => term), (natural, natural))
  =
  (collapse[(natural, natural),
             (Substate,
               Unit =>
                 term)](select_weight[((natural, natural)) =>
((Substate, Unit => term),
  (natural,
    natural))](List((one_natural,
                      ((a: (natural, natural)) =>
                        ((state_s(),
                           ((_: Unit) =>
                             Const("Event_States.Substate.state__S",
                                    Typerepb("Event_States.Substate", Nil)))),
                          a))),
                     (one_natural,
                       ((a: (natural, natural)) =>
                         ((state_t(),
                            ((_: Unit) =>
                              Const("Event_States.Substate.state__T",
                                     Typerepb("Event_States.Substate", Nil)))),
                           a))))))).apply(s)

def random_substate(i: natural):
      ((natural, natural)) => ((Substate, Unit => term), (natural, natural))
  =
  ((a: (natural, natural)) => random_aux_substate(i, i, a))

def valapp[A, B](x0: (A => B, Unit => term), x1: (A, Unit => term)):
      (B, Unit => term)
  =
  (x0, x1) match {
  case ((f, tf), (x, tx)) => (f(x), ((_: Unit) => App(tf(()), tx(()))))
}

def random_aux_state(i: natural, j: natural, s: (natural, natural)):
      ((State, Unit => term), (natural, natural))
  =
  (collapse[(natural, natural),
             (State,
               Unit =>
                 term)](select_weight[((natural, natural)) =>
((State, Unit => term),
  (natural,
    natural))](List((one_natural,
                      scomp[(natural, natural), (Substate, Unit => term),
                             (natural, natural),
                             ((State, Unit => term),
                               (natural,
                                 natural))](random_substate(j),
     ((x: (Substate, Unit => term)) =>
       ((a: (natural, natural)) =>
         (valapp[Substate,
                  State]((((aa: Substate) => Stateconstr(aa)),
                           ((_: Unit) =>
                             Const("Event_States.State.StateConstr",
                                    Typerepb("fun",
      List(Typerepb("Event_States.Substate", Nil),
            Typerepb("Event_States.State", Nil)))))),
                          x),
           a))))))))).apply(s)

def random_statea(i: natural):
      ((natural, natural)) => ((State, Unit => term), (natural, natural))
  =
  ((a: (natural, natural)) => random_aux_state(i, i, a))

trait random[A] extends typerep[A] {
  val `def_automaton_Event_scalaExec.random`:
        (natural, (natural, natural)) => ((A, Unit => term), (natural, natural))
}
def random[A](a: natural, b: (natural, natural))(implicit A: random[A]):
      ((A, Unit => term), (natural, natural))
  = A.`def_automaton_Event_scalaExec.random`(a, b)
object random{
  implicit def `def_automaton_Event_scalaExec.random_state`: random[State] = new
    random[State] {
    val `def_automaton_Event_scalaExec.random` =
      (a: natural, b: (natural, natural)) => (random_statea(a)).apply(b)
    val `def_automaton_Event_scalaExec.typerep` = (a: itself[State]) =>
      typerep_statea(a)
  }
}

abstract sealed class channels
final case class beinchannel_rep() extends channels

def enum_channelsb: List[channels] = List(beinchannel_rep())

def list_all[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

def enum_all_channels(p: channels => Boolean): Boolean =
  list_all[channels](p, enum_channelsb)

def list_ex[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => false
  case (p, x :: xs) => p(x) || list_ex[A](p, xs)
}

def enum_ex_channels(p: channels => Boolean): Boolean =
  list_ex[channels](p, enum_channelsb)

def equal_channelsb(x0: channels, x1: channels): Boolean = (x0, x1) match {
  case (beinchannel_rep(), beinchannel_rep()) => true
}

def bot_set[A]: set[A] = seta[A](Nil)

def removeall[A : equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeall[A](x, xs) else y :: removeall[A](x, xs))
}

def membera[A : equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def inserta[A : equal](x: A, xs: List[A]): List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeall[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def chandom_channels(a: myself[channels]): set[channel] =
  insert[channel](CH(List(Chara(false, true, false, false, false, true, true,
                                 false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(true, false, false, true, false, false, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(true, true, false, false, false, false, true,
                                  false),
                           Chara(false, false, false, true, false, true, true,
                                  false),
                           Chara(true, false, false, false, false, true, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(false, false, true, true, false, true, true,
                                  false)),
                      Ttlive(), Tboolevent()),
                   bot_set[channel])

def Rep_channelsb(x0: channels): channel = x0 match {
  case beinchannel_rep() =>
    CH(List(Chara(false, true, false, false, false, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(true, false, false, true, false, false, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(true, true, false, false, false, false, true, false),
             Chara(false, false, false, true, false, true, true, false),
             Chara(true, false, false, false, false, true, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(false, false, true, true, false, true, true, false)),
        Ttlive(), Tboolevent())
}

def Abs_channels(x0: channel): channels = x0 match {
  case CH(List(Chara(false, true, false, false, false, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(true, false, false, true, false, false, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(true, true, false, false, false, false, true, false),
                Chara(false, false, false, true, false, true, true, false),
                Chara(true, false, false, false, false, true, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(false, false, true, true, false, true, true, false)),
           Ttlive(), Tboolevent())
    => beinchannel_rep()
}

trait one_chan[A] extends chan[A] {
}
object one_chan{
  implicit def
    `def_automaton_Event_scalaExec.one_chan_channelsa`: one_chan[channelsa] =
    new one_chan[channelsa] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channelsa) => Rep_channelsc(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channelsa(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def
    `def_automaton_Event_scalaExec.one_chan_channels`: one_chan[channels] = new
    one_chan[channels] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channels) => Rep_channelsb(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channels(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channels]) =>
      chandom_channels(a)
  }
}

trait tchan[A] extends chan[A] {
}
object tchan{
  implicit def
    `def_automaton_Event_scalaExec.tchan_tstimed`[A : enum : one_chan]:
      tchan[tstimed[A]]
    = new tchan[tstimed[A]] {
    val `def_automaton_Event_scalaExec.Rep` = (a: tstimed[A]) =>
      Rep_tstimeda[A](a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_tstimed[A](a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[tstimed[A]]) =>
      chandom_tstimed[A](a)
  }
  implicit def `def_automaton_Event_scalaExec.tchan_channelsa`: tchan[channelsa]
    = new tchan[channelsa] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channelsa) => Rep_channelsc(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channelsa(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `def_automaton_Event_scalaExec.tchan_channels`: tchan[channels] =
    new tchan[channels] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channels) => Rep_channelsb(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channels(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channels]) =>
      chandom_channels(a)
  }
}

trait echan[A] extends tchan[A] with one_chan[A] {
}
object echan{
  implicit def `def_automaton_Event_scalaExec.echan_channelsa`: echan[channelsa]
    = new echan[channelsa] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channelsa) => Rep_channelsc(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channelsa(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channelsa]) =>
      chandom_channelsa(a)
  }
  implicit def `def_automaton_Event_scalaExec.echan_channels`: echan[channels] =
    new echan[channels] {
    val `def_automaton_Event_scalaExec.Rep` = (a: channels) => Rep_channelsb(a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_channels(a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[channels]) =>
      chandom_channels(a)
  }
}

def one_integera: BigInt = BigInt(1)

trait one[A] {
  val `def_automaton_Event_scalaExec.one`: A
}
def one[A](implicit A: one[A]): A = A.`def_automaton_Event_scalaExec.one`
object one{
  implicit def `def_automaton_Event_scalaExec.one_integer`: one[BigInt] = new
    one[BigInt] {
    val `def_automaton_Event_scalaExec.one` = one_integera
  }
}

trait numeral[A] extends one[A] with semigroup_add[A] {
}
object numeral{
  implicit def `def_automaton_Event_scalaExec.numeral_integer`: numeral[BigInt]
    = new numeral[BigInt] {
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
    val `def_automaton_Event_scalaExec.one` = one_integera
  }
}

trait times[A] {
  val `def_automaton_Event_scalaExec.times`: (A, A) => A
}
def times[A](a: A, b: A)(implicit A: times[A]): A =
  A.`def_automaton_Event_scalaExec.times`(a, b)
object times{
  implicit def `def_automaton_Event_scalaExec.times_integer`: times[BigInt] =
    new times[BigInt] {
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
  }
}

trait power[A] extends one[A] with times[A] {
}
object power{
  implicit def `def_automaton_Event_scalaExec.power_integer`: power[BigInt] =
    new power[BigInt] {
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
    val `def_automaton_Event_scalaExec.one` = one_integera
  }
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}
object ab_semigroup_add{
  implicit def
    `def_automaton_Event_scalaExec.ab_semigroup_add_integer`:
      ab_semigroup_add[BigInt]
    = new ab_semigroup_add[BigInt] {
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
  }
}

trait semigroup_mult[A] extends times[A] {
}
object semigroup_mult{
  implicit def
    `def_automaton_Event_scalaExec.semigroup_mult_integer`:
      semigroup_mult[BigInt]
    = new semigroup_mult[BigInt] {
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
  }
}

trait semiring[A] extends ab_semigroup_add[A] with semigroup_mult[A] {
}
object semiring{
  implicit def
    `def_automaton_Event_scalaExec.semiring_integer`: semiring[BigInt] = new
    semiring[BigInt] {
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
  }
}

trait mult_zero[A] extends times[A] with zero[A] {
}
object mult_zero{
  implicit def
    `def_automaton_Event_scalaExec.mult_zero_integer`: mult_zero[BigInt] = new
    mult_zero[BigInt] {
    val `def_automaton_Event_scalaExec.zero` = BigInt(0)
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
  }
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}
object comm_monoid_add{
  implicit def
    `def_automaton_Event_scalaExec.comm_monoid_add_integer`:
      comm_monoid_add[BigInt]
    = new comm_monoid_add[BigInt] {
    val `def_automaton_Event_scalaExec.zero` = BigInt(0)
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
  }
}

trait semiring_0[A]
  extends comm_monoid_add[A] with mult_zero[A] with semiring[A] {
}
object semiring_0{
  implicit def
    `def_automaton_Event_scalaExec.semiring_0_integer`: semiring_0[BigInt] = new
    semiring_0[BigInt] {
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
    val `def_automaton_Event_scalaExec.zero` = BigInt(0)
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
  }
}

trait monoid_mult[A] extends semigroup_mult[A] with power[A] {
}
object monoid_mult{
  implicit def
    `def_automaton_Event_scalaExec.monoid_mult_integer`: monoid_mult[BigInt] =
    new monoid_mult[BigInt] {
    val `def_automaton_Event_scalaExec.one` = one_integera
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
  }
}

trait semiring_numeral[A]
  extends monoid_mult[A] with numeral[A] with semiring[A] {
}
object semiring_numeral{
  implicit def
    `def_automaton_Event_scalaExec.semiring_numeral_integer`:
      semiring_numeral[BigInt]
    = new semiring_numeral[BigInt] {
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
    val `def_automaton_Event_scalaExec.one` = one_integera
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
  }
}

trait zero_neq_one[A] extends one[A] with zero[A] {
}
object zero_neq_one{
  implicit def
    `def_automaton_Event_scalaExec.zero_neq_one_integer`: zero_neq_one[BigInt] =
    new zero_neq_one[BigInt] {
    val `def_automaton_Event_scalaExec.zero` = BigInt(0)
    val `def_automaton_Event_scalaExec.one` = one_integera
  }
}

trait semiring_1[A]
  extends semiring_numeral[A] with semiring_0[A] with zero_neq_one[A] {
}
object semiring_1{
  implicit def
    `def_automaton_Event_scalaExec.semiring_1_integer`: semiring_1[BigInt] = new
    semiring_1[BigInt] {
    val `def_automaton_Event_scalaExec.zero` = BigInt(0)
    val `def_automaton_Event_scalaExec.one` = one_integera
    val `def_automaton_Event_scalaExec.times` = (a: BigInt, b: BigInt) => a * b
    val `def_automaton_Event_scalaExec.plus` = (a: BigInt, b: BigInt) => a + b
  }
}

abstract sealed class channelsa
final case class beoutchannel_rep() extends channelsa

def enum_channelsc: List[channelsa] = List(beoutchannel_rep())

def enum_all_channelsa(p: channelsa => Boolean): Boolean =
  list_all[channelsa](p, enum_channelsc)

def enum_ex_channelsa(p: channelsa => Boolean): Boolean =
  list_ex[channelsa](p, enum_channelsc)

def equal_channelsc(x0: channelsa, x1: channelsa): Boolean = (x0, x1) match {
  case (beoutchannel_rep(), beoutchannel_rep()) => true
}

def chandom_channelsa(a: myself[channelsa]): set[channel] =
  insert[channel](CH(List(Chara(false, true, false, false, false, true, true,
                                 false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(true, true, true, true, false, false, true,
                                  false),
                           Chara(true, false, true, false, true, true, true,
                                  false),
                           Chara(false, false, true, false, true, true, true,
                                  false),
                           Chara(true, true, false, false, false, false, true,
                                  false),
                           Chara(false, false, false, true, false, true, true,
                                  false),
                           Chara(true, false, false, false, false, true, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(false, true, true, true, false, true, true,
                                  false),
                           Chara(true, false, true, false, false, true, true,
                                  false),
                           Chara(false, false, true, true, false, true, true,
                                  false)),
                      Ttlive(), Tboolevent()),
                   bot_set[channel])

def Rep_channelsc(x0: channelsa): channel = x0 match {
  case beoutchannel_rep() =>
    CH(List(Chara(false, true, false, false, false, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(true, true, true, true, false, false, true, false),
             Chara(true, false, true, false, true, true, true, false),
             Chara(false, false, true, false, true, true, true, false),
             Chara(true, true, false, false, false, false, true, false),
             Chara(false, false, false, true, false, true, true, false),
             Chara(true, false, false, false, false, true, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(false, true, true, true, false, true, true, false),
             Chara(true, false, true, false, false, true, true, false),
             Chara(false, false, true, true, false, true, true, false)),
        Ttlive(), Tboolevent())
}

def Abs_channelsa(x0: channel): channelsa = x0 match {
  case CH(List(Chara(false, true, false, false, false, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(true, true, true, true, false, false, true, false),
                Chara(true, false, true, false, true, true, true, false),
                Chara(false, false, true, false, true, true, true, false),
                Chara(true, true, false, false, false, false, true, false),
                Chara(false, false, false, true, false, true, true, false),
                Chara(true, false, false, false, false, true, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(false, true, true, true, false, true, true, false),
                Chara(true, false, true, false, false, true, true, false),
                Chara(false, false, true, true, false, true, true, false)),
           Ttlive(), Tboolevent())
    => beoutchannel_rep()
}

abstract sealed class tstimed[A]
final case class TSTIMEDA[A](a: A) extends tstimed[A]

def enum_all_tstimed[A : enum : one_chan](p: (tstimed[A]) => Boolean): Boolean =
  enum_all[A](((c: A) => p(TSTIMEDA[A](c))))

def enum_ex_tstimed[A : enum : one_chan](p: (tstimed[A]) => Boolean): Boolean =
  enum_ex[A](((c: A) => p(TSTIMEDA[A](c))))

def enum_tstimeda[A : enum : one_chan]: List[tstimed[A]] =
  map[A, tstimed[A]](((a: A) => TSTIMEDA[A](a)), enum[A])

def equal_tstimeda[A : equal : one_chan](x0: tstimed[A], x1: tstimed[A]):
      Boolean
  =
  (x0, x1) match {
  case (TSTIMEDA(x), TSTIMEDA(ya)) => eq[A](x, ya)
}

def changetimetype(tt: timetype, x1: channel): channel = (tt, x1) match {
  case (tt, CH(name, uu, p)) => CH(name, tt, p)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def chandom_tstimed[A : one_chan](uu: myself[tstimed[A]]): set[channel] =
  image[channel,
         channel](((a: channel) => changetimetype(Ttfin(), a)),
                   chandom[A](DUMMY[A]()))

def member[A : equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def Rep_tstimeda[A : one_chan](x0: tstimed[A]): channel = x0 match {
  case TSTIMEDA(cs) =>
    (if (member[channel](Rep[A](cs), chandom[A](DUMMY[A]())))
      changetimetype(Ttfin(), Rep[A](cs)) else Rep[A](cs))
}

def less_eq_set[A : equal](a: set[A], b: set[A]): Boolean = (a, b) match {
  case (coset(Nil), seta(Nil)) => false
  case (a, coset(ys)) => list_all[A](((y: A) => ! (member[A](y, a))), ys)
  case (seta(xs), b) => list_all[A](((x: A) => member[A](x, b)), xs)
}

def equal_set[A : equal](a: set[A], b: set[A]): Boolean =
  less_eq_set[A](a, b) && less_eq_set[A](b, a)

def cname(x0: channel): List[char] = x0 match {
  case CH(name, uu, uv) => name
}

def top_set[A]: set[A] = coset[A](Nil)

def cmsgt(x0: msgtype): set[M_pure] = x0 match {
  case Tboolevent() =>
    image[Boolean,
           M_pure](((a: Boolean) => booleventconstr(a)), top_set[Boolean])
  case Tboolsync() =>
    image[Boolean,
           M_pure](((a: Boolean) => boolsyncconstr(a)), top_set[Boolean])
  case Tnatevent() =>
    image[nat, M_pure](((a: nat) => nateventconstr(a)), top_set[nat])
  case Tnatsync() =>
    image[nat, M_pure](((a: nat) => natsyncconstr(a)), top_set[nat])
  case Tstringevent() =>
    image[List[char],
           M_pure](((a: List[char]) => stringeventconstr(a)),
                    top_set[List[char]])
  case Tstringsync() =>
    image[List[char],
           M_pure](((a: List[char]) => stringsyncconstr(a)),
                    top_set[List[char]])
  case Tnone() => bot_set[M_pure]
}

def cmsg(x0: channel): set[M_pure] = x0 match {
  case CH(uu, uv, mt) => cmsgt(mt)
}

def enum_the[A](a: A => Boolean): A = sys.error("Enum.enum_the")

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def The[A : enum](p: A => Boolean): A = (filter[A](p, enum[A]) match {
   case Nil => enum_the[A](p)
   case List(x) => x
   case _ :: _ :: _ => enum_the[A](p)
 })

def Abs_tstimed[A : enum : one_chan](cs: channel): tstimed[A] =
  (if (member[channel](cs, chandom_tstimed[A](DUMMY[tstimed[A]]())))
    TSTIMEDA[A](The[A](((a: A) =>
                         equal_lista[char](cname(Rep[A](a)), cname(cs)) &&
                           equal_set[M_pure](cmsg(Rep[A](a)), cmsg(cs)))))
    else TSTIMEDA[A](Abs[A](cs)))

trait tschan[A] extends tchan[A] {
}
object tschan{
  implicit def
    `def_automaton_Event_scalaExec.tschan_tstimed`[A : enum : one_chan]:
      tschan[tstimed[A]]
    = new tschan[tstimed[A]] {
    val `def_automaton_Event_scalaExec.Rep` = (a: tstimed[A]) =>
      Rep_tstimeda[A](a)
    val `def_automaton_Event_scalaExec.Abs` = (a: channel) => Abs_tstimed[A](a)
    val `def_automaton_Event_scalaExec.chandom` = (a: myself[tstimed[A]]) =>
      chandom_tstimed[A](a)
  }
}

abstract sealed class eventwithchan[A]
final case class Abs_eventwithchan[A](a: (A, M_pure)) extends eventwithchan[A]

def equal_eventwithchana[A : chan](ec1: eventwithchan[A],
                                    ec2: eventwithchan[A]):
      Boolean
  =
  equal_eventwithchana[A](ec1, ec2)

abstract sealed class u[A]
final case class Ibottom[A]() extends u[A]
final case class Iup[A](a: A) extends u[A]

abstract sealed class eventwellstream[A]
final case class Abs_eventwellstream[A](a: stream[event[(A, M_pure)]]) extends
  eventwellstream[A]

abstract sealed class execautomaton_ext[A, B, C, D]
final case class execautomaton_exta[A, B, C,
                                     D](a: A => B => natural => (A, C),
 b: natural => (A, C), c: D)
  extends execautomaton_ext[A, B, C, D]

abstract sealed class listautomaton_ext[A, B, C, D]
final case class listautomaton_exta[A, B, C,
                                     D](a: A => B => List[(A, C)],
 b: List[(A, C)], c: D)
  extends listautomaton_ext[A, B, C, D]

abstract sealed class dautomaton_ext[A, B, C, D]
final case class dautomaton_exta[A, B, C,
                                  D](a: A => B => (A, C), b: (A, C), c: D)
  extends dautomaton_ext[A, B, C, D]

def nth[A](x0: List[A], x1: nat): A = (x0, x1) match {
  case (x :: xs, Suc(n)) => nth[A](xs, n)
  case (x :: xs, zero_nat()) => x
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def rnd[A : random](seed: (natural, natural)): A =
  fst[A, Unit =>
           term](fst[(A, Unit => term),
                      (natural,
                        natural)](random[A](natural_of_integer(BigInt(1000)),
     seed)))

def Rep_sbelem[A : chan](x0: sbelem[A]): Option[A => M] = x0 match {
  case Abs_sbelem(x) => x
}

def sbelem_none[A : chan]: sbelem[A] =
  Abs_sbelem[A]((if (equal_set[channel](chandom[A](DUMMY[A]()),
 bot_set[channel]))
                  None else Rep_sbelem[A](sys.error("undefined"))))

def shd_nc[A : countable](x0: stream[A]): A = x0 match {
  case lscons_u_nc(a, b) => a
}

def equal_stream[A : countable : equal](a: stream[A], b: stream[A]): Boolean =
  StreamEqual.streamequal[A](a, b)

def sbhdelemwell[A : chan : enum](sb: sb[A]): Boolean =
  All[A](((c: A) =>
           ! (equal_stream[M]((Rep_sb[A](sb)).apply(c),
                               stream_bottom_nc[M]()))))

def shd_elem[A : chan : enum](sb: sb[A]): sbelem[A] =
  Abs_sbelem[A]((if (! (sbhdelemwell[A](sb)))
                  Rep_sbelem[A](sys.error("undefined"))
                  else Some[A => M](((c: A) =>
                                      shd_nc[M]((Rep_sb[A](sb)).apply(c))))))

def sbhdelem_h[A : chan : enum](sb: sb[A]): u[sbelem[A]] =
  (if (equal_set[channel](chandom[A](DUMMY[A]()), bot_set[channel]))
    Iup[sbelem[A]](sbelem_none[A])
    else (if (! (sbhdelemwell[A](sb))) Ibottom[sbelem[A]]()
           else Iup[sbelem[A]](shd_elem[A](sb))))

def sbhdelem[A : chan : enum : equal](sb: sb[A]): sbelem[A] =
  {
    val (Iup(sbElem)): u[sbelem[A]] = sbhdelem_h[A](sb);
    sbElem
  }

def sup[A : countable](a: A): stream[A] =
  lscons_u_nc[A](a, stream_bottom_nc[A]())

def list2s[A : countable](x0: List[A]): stream[A] = x0 match {
  case Nil => stream_bottom_nc[A]()
  case a :: as => lscons_u_nc[A](a, list2s[A](as))
}

def gen_length[A](n: nat, x1: List[A]): nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Suc(n), xs)
  case (n, Nil) => n
}

def thea[A](x0: Option[A]): A = x0 match {
  case Some(x2) => x2
}

def Rep_eventwithchan[A : chan](x0: eventwithchan[A]): (A, M_pure) = x0 match {
  case Abs_eventwithchan(x) => x
}

def efilter_nc[A : countable](p: A => Boolean, x1: stream[event[A]]):
      stream[event[A]]
  =
  (p, x1) match {
  case (p, lscons_u_nc(Tick(), as)) =>
    sconc_nc[event[A]](sup[event[A]](Tick[A]()), efilter_nc[A](p, as))
  case (p, lscons_u_nc(Eventa(a), as)) =>
    (if (p(a))
      sconc_nc[event[A]](sup[event[A]](Eventa[A](a)), efilter_nc[A](p, as))
      else efilter_nc[A](p, as))
  case (p, stream_bottom_nc()) => stream_bottom_nc[event[A]]()
}

def smap_nc[A : countable, B : countable](f: A => B, x1: stream[A]): stream[B] =
  (f, x1) match {
  case (f, stream_bottom_nc()) => stream_bottom_nc[B]()
  case (f, lscons_u_nc(a, as)) =>
    sconc_nc[B](sup[B](f(a)), smap_nc[A, B](f, as))
}

def map_event[A, B](f: A => B, x1: event[A]): event[B] = (f, x1) match {
  case (f, Eventa(x1)) => Eventa[B](f(x1))
  case (f, Tick()) => Tick[B]()
}

def emap_nc[A : countable, B : countable](f: A => B, s: stream[event[A]]):
      stream[event[B]]
  =
  smap_nc[event[A], event[B]](((a: event[A]) => map_event[A, B](f, a)), s)

def ssplit_nc[A : echan : finite : equal](s: stream[event[eventwithchan[A]]]):
      sb[A]
  =
  Abs_sb[A]((if (equal_set[channel](chandom[A](DUMMY[A]()), bot_set[channel]))
              ((_: A) => stream_bottom_nc[M]())
              else ((c: A) =>
                     smap_nc[event[M_pure],
                              M](comp[M_timed, M,
                                       event[M_pure]](((a: M_timed) =>
                Timed(a)),
               ((a: event[M_pure]) => Tlive(a))),
                                  emap_nc[(A, M_pure),
   M_pure](((a: (A, M_pure)) => snd[A, M_pure](a)),
            efilter_nc[(A, M_pure)](((a: (A, M_pure)) =>
                                      {
val (x, _): (A, M_pure) = a;
eq[A](x, c)
                                      }),
                                     emap_nc[eventwithchan[A],
      (A, M_pure)](((a: eventwithchan[A]) => Rep_eventwithchan[A](a)), s)))))))

def ssplit[A : echan : enum : equal]:
      cfun[stream[event[eventwithchan[A]]], sb[A]]
  =
  Abs_cfun[stream[event[eventwithchan[A]]],
            sb[A]](((a: stream[event[eventwithchan[A]]]) => ssplit_nc[A](a)))

def Rep_cfun[B : cpo, A : cpo](x0: cfun[B, A]): B => A = x0 match {
  case Abs_cfun(x) => x
}

def channelschan[A, B](boolEVENTConv: A => B, beInChannel_pattern: A,
                        x2: channels):
      B
  =
  (boolEVENTConv, beInChannel_pattern, x2) match {
  case (boolEVENTConv, beInChannel_pattern, beinchannel_rep()) =>
    boolEVENTConv(beInChannel_pattern)
}

def buildsb: (stream[event[Boolean]]) => channels => stream[M] =
  ((a: stream[event[Boolean]]) => (b: channels) =>
    channelschan[stream[event[Boolean]],
                  stream[M]](((aa: stream[event[Boolean]]) =>
                               smap_nc[event[Boolean],
M](comp[event[M_pure], M,
         event[Boolean]](comp[M_timed, M,
                               event[M_pure]](((ab: M_timed) => Timed(ab)),
       ((ab: event[M_pure]) => Tlive(ab))),
                          ((ab: event[Boolean]) =>
                            map_event[Boolean,
                                       M_pure](((ac: Boolean) =>
         booleventconstr(ac)),
        ab))),
    aa)),
                              a, b))

def of_nat_aux[A : semiring_1](inc: A => A, x1: nat, i: A): A = (inc, x1, i)
  match {
  case (inc, zero_nat(), i) => i
  case (inc, Suc(n), i) => of_nat_aux[A](inc, n, inc(i))
}

def of_nat[A : semiring_1](n: nat): A =
  of_nat_aux[A](((i: A) => plus[A](i, one[A])), n, zero[A])

def integer_of_nat: nat => BigInt = ((a: nat) => of_nat[BigInt](a))

def natural_of_nat(n: nat): natural =
  natural_of_integer(integer_of_nat.apply(n))

def plus_nat(x0: nat, n: nat): nat = (x0, n) match {
  case (Suc(m), n) => plus_nat(m, Suc(n))
  case (zero_nat(), n) => n
}

def one_nat: nat = Suc(zero_nat())

def nat_of_integer(k: BigInt): nat =
  (if (k <= BigInt(0)) zero_nat()
    else {
           val (l, j): (BigInt, BigInt) = divmod_integer(k, BigInt(2))
           val la: nat = nat_of_integer(l)
           val lb: nat = plus_nat(la, la);
           (if (j == BigInt(0)) lb else plus_nat(lb, one_nat))
         })

def nat_of_natural: natural => nat =
  comp[BigInt, nat,
        natural](((a: BigInt) => nat_of_integer(a)),
                  ((a: natural) => integer_of_natural(a)))

def size_list[A]: (List[A]) => nat =
  ((a: List[A]) => gen_length[A](zero_nat(), a))

def listfun[A](list: List[A], n: natural): A =
  nth[A](list,
          nat_of_natural.apply(modulo_natural(n,
       natural_of_nat(size_list[A].apply(list)))))

def apfst[A, B, C](f: A => B, x1: (A, C)): (B, C) = (f, x1) match {
  case (f, (x, y)) => (f(x), y)
}

def insbsetter_nc(a: stream[event[Boolean]]): sb[channels] =
  Abs_sb[channels](buildsb.apply(a))

def sbsetter: cfun[stream[event[Boolean]], sb[channels]] =
  Abs_cfun[stream[event[Boolean]],
            sb[channels]](((a: stream[event[Boolean]]) => insbsetter_nc(a)))

def exauttransition[A, B, C : conc, D](x0: execautomaton_ext[A, B, C, D]):
      A => B => natural => (A, C)
  =
  x0 match {
  case execautomaton_exta(exautTransition, exautInitConfig, more) =>
    exautTransition
}

def rndtransition[A, B,
                   C : conc](eaut: execautomaton_ext[A, B, C, Unit],
                              x1: (A, (natural, natural)), msg: B):
      ((A, (natural, natural)), C)
  =
  (eaut, x1, msg) match {
  case (eaut, (state, seed), msg) =>
    {
      val (nat, nextSeed): (natural, (natural, natural)) = next(seed);
      apfst[A, (A, (natural, natural)),
             C](((s: A) => (s, nextSeed)),
                 (exauttransition[A, B, C,
                                   Unit](eaut)).apply(state).apply(msg).apply(nat))
    }
}

def exautinitconfig[A, B, C : conc, D](x0: execautomaton_ext[A, B, C, D]):
      natural => (A, C)
  =
  x0 match {
  case execautomaton_exta(exautTransition, exautInitConfig, more) =>
    exautInitConfig
}

def rndinitconfig[A, B,
                   C : conc](eaut: execautomaton_ext[A, B, C, Unit],
                              seed: (natural, natural)):
      ((A, (natural, natural)), C)
  =
  {
    val (nat, nextSeed): (natural, (natural, natural)) = next(seed);
    apfst[A, (A, (natural, natural)),
           C](((s: A) => (s, nextSeed)),
               (exautinitconfig[A, B, C, Unit](eaut)).apply(nat))
  }

def exectoda[A, B,
              C : conc](aut: execautomaton_ext[A, B, C, Unit],
                         seed: (natural, natural)):
      dautomaton_ext[(A, (natural, natural)), B, C, Unit]
  =
  dautomaton_exta[(A, (natural, natural)), B, C,
                   Unit](((a: (A, (natural, natural))) => (b: B) =>
                           rndtransition[A, B, C](aut, a, b)),
                          rndinitconfig[A, B, C](aut, seed), ())

def sdrop_nc[A : countable](n: nat, s: stream[A]): stream[A] = (n, s) match {
  case (n, stream_bottom_nc()) => stream_bottom_nc[A]()
  case (zero_nat(), s) => s
  case (Suc(n), lscons_u_nc(a, b)) => sdrop_nc[A](n, b)
}

def sbdrop_nc[A : chan](a: nat, b: sb[A]): sb[A] =
  Abs_sb[A](((c: A) => sdrop_nc[M](a, (Rep_sb[A](b)).apply(c))))

def m2list(x0: M): List[M_pure] = x0 match {
  case Timed(Tfin(ls)) => ls
  case Timed(Tlive(Eventa(e))) => List(e)
  case Timed(Tlive(Tick())) => Nil
  case Untimed(e) => List(e)
  case Timed(Tsyna(Msg(m))) => List(m)
  case Timed(Tsyna(eps())) => Nil
  case Timed(Tone(va)) => List(va)
}

def conv_bool(x0: M): event[Boolean] = x0 match {
  case Timed(Tlive(Eventa(booleventconstr(a)))) => Eventa[Boolean](a)
  case Timed(Tlive(Tick())) => Tick[Boolean]()
  case Untimed(va) => conv_bool(Untimed(va))
  case Timed(Tsyna(vb)) => conv_bool(Timed(Tsyna(vb)))
  case Timed(Tone(vb)) => conv_bool(Timed(Tone(vb)))
  case Timed(Tlive(Eventa(boolsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](boolsyncconstr(vd)))))
  case Timed(Tlive(Eventa(nateventconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](nateventconstr(vd)))))
  case Timed(Tlive(Eventa(natsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](natsyncconstr(vd)))))
  case Timed(Tlive(Eventa(stringeventconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](stringeventconstr(vd)))))
  case Timed(Tlive(Eventa(stringsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](stringsyncconstr(vd)))))
  case Timed(Tfin(vb)) => conv_bool(Timed(Tfin(vb)))
}

def conv_boola(x0: M): event[Boolean] = x0 match {
  case Timed(Tlive(Eventa(booleventconstr(a)))) => Eventa[Boolean](a)
  case Timed(Tlive(Tick())) => Tick[Boolean]()
  case Untimed(va) => conv_bool(Untimed(va))
  case Timed(Tsyna(vb)) => conv_bool(Timed(Tsyna(vb)))
  case Timed(Tone(vb)) => conv_bool(Timed(Tone(vb)))
  case Timed(Tlive(Eventa(boolsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](boolsyncconstr(vd)))))
  case Timed(Tlive(Eventa(nateventconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](nateventconstr(vd)))))
  case Timed(Tlive(Eventa(natsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](natsyncconstr(vd)))))
  case Timed(Tlive(Eventa(stringeventconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](stringeventconstr(vd)))))
  case Timed(Tlive(Eventa(stringsyncconstr(vd)))) =>
    conv_bool(Timed(Tlive(Eventa[M_pure](stringsyncconstr(vd)))))
  case Timed(Tfin(vb)) => conv_bool(Timed(Tfin(vb)))
}

def sbgetter: cfun[sb[channelsa], stream[event[Boolean]]] =
  Abs_cfun[sb[channelsa],
            stream[event[Boolean]]](((a: sb[channelsa]) =>
                                      smap_nc[M,
       event[Boolean]](((aa: M) => conv_boola(aa)),
                        (Rep_sb[channelsa](a)).apply(beoutchannel_rep()))))

def sbgetch_nc[A : chan, B : chan](c: A, sb: sb[B]): stream[M] =
  (if (member[channel](Rep[A](c), chandom[B](DUMMY[B]())))
    (Rep_sb[B](sb)).apply(Abs[B](Rep[A](c))) else stream_bottom_nc[M]())

def m2event(x0: M): event[M_pure] = x0 match {
  case Timed(Tlive(e)) => e
  case Timed(Tfin(Nil)) => Tick[M_pure]()
  case Timed(Tfin(x :: xs)) => Eventa[M_pure](x)
  case Untimed(e) => Eventa[M_pure](e)
  case Timed(Tsyna(eps())) => Tick[M_pure]()
  case Timed(Tsyna(Msg(v))) => sys.error("undefined")
  case Timed(Tone(va)) => Eventa[M_pure](va)
}

def sbelist[A : tschan : enum](c: A, sbe: sbelem[A]): List[M_pure] =
  m2list((if (member[channel](Rep[A](c), chandom[A](DUMMY[A]())))
           (thea[A => M](Rep_sbelem[A](sbe))).apply(c)
           else sys.error("undefined")))

def listmerge[A](x0: List[A], b: List[A]): List[List[A]] = (x0, b) match {
  case (Nil, b) => List(b)
  case (v :: va, Nil) => List(v :: va)
  case (a :: as, b :: bs) =>
    map[List[A],
         List[A]](((ba: List[A]) => a :: ba), listmerge[A](as, b :: bs)) ++
      map[List[A],
           List[A]](((aa: List[A]) => b :: aa), listmerge[A](a :: as, bs))
}

def tsmerge[A](x0: List[List[A]]): List[List[A]] = x0 match {
  case Nil => List(Nil)
  case List(a) => List(a)
  case a :: b :: ls =>
    maps[List[A],
          List[A]](((merged: List[A]) => tsmerge[A](merged :: ls)),
                    listmerge[A](a, b))
}

def listtransition[A, B, C : conc, D](x0: listautomaton_ext[A, B, C, D]):
      A => B => List[(A, C)]
  =
  x0 match {
  case listautomaton_exta(listTransition, listInitConfig, more) =>
    listTransition
}

def listinitconfig[A, B, C : conc, D](x0: listautomaton_ext[A, B, C, D]):
      List[(A, C)]
  =
  x0 match {
  case listautomaton_exta(listTransition, listInitConfig, more) =>
    listInitConfig
}

def listtoexec[A, B, C : conc](laut: listautomaton_ext[A, B, C, Unit]):
      execautomaton_ext[A, B, C, Unit]
  =
  execautomaton_exta[A, B, C,
                      Unit](((state: A) => (msg: B) =>
                              ((a: natural) =>
                                listfun[(A,
  C)]((listtransition[A, B, C, Unit](laut)).apply(state).apply(msg), a))),
                             ((a: natural) =>
                               listfun[(A,
 C)](listinitconfig[A, B, C, Unit](laut), a)),
                             ())

def mergetrans[A : countable](ls: List[List[A]]): List[(Unit, stream[List[A]])]
  =
  map[List[A],
       (Unit,
         stream[List[A]])](((l: List[A]) => ((), sup[List[A]](l))),
                            tsmerge[A](ls))

def mergeaut[A : countable]:
      listautomaton_ext[Unit, List[List[A]], stream[List[A]], Unit]
  =
  listautomaton_exta[Unit, List[List[A]], stream[List[A]],
                      Unit](((_: Unit) =>
                              ((a: List[List[A]]) => mergetrans[A](a))),
                             List(((), stream_bottom_nc[List[A]]())), ())

def convtrans[A : tschan : enum](sbe: sbelem[A]): List[List[(A, M_pure)]] =
  (if (equal_set[channel](chandom[A](DUMMY[A]()), bot_set[channel])) Nil
    else map[A, List[(A, M_pure)]](((c: A) =>
                                     map[M_pure,
  (A, M_pure)](((a: M_pure) => (c, a)), sbelist[A](c, sbe))),
                                    enum[A]))

def convertaut[A : tschan : enum]:
      dautomaton_ext[Unit, sbelem[A], stream[List[List[(A, M_pure)]]], Unit]
  =
  dautomaton_exta[Unit, sbelem[A], stream[List[List[(A, M_pure)]]],
                   Unit](((_: Unit) => (sb: sbelem[A]) =>
                           ((), sup[List[List[(A,
        M_pure)]]](convtrans[A](sb)))),
                          ((), stream_bottom_nc[List[List[(A, M_pure)]]]()), ())

def dautinitconfig[A, B, C : conc, D](x0: dautomaton_ext[A, B, C, D]): (A, C) =
  x0 match {
  case dautomaton_exta(dautTransition, dautInitConfig, more) => dautInitConfig
}

def dauttransition[A, B, C : conc, D](x0: dautomaton_ext[A, B, C, D]):
      A => B => (A, C)
  =
  x0 match {
  case dautomaton_exta(dautTransition, dautInitConfig, more) => dautTransition
}

def tsexecstatesem_nc[A, B : chan : enum : equal,
                       C : bot_nc : conc](aut:
    dautomaton_ext[A, sbelem[B], C, Unit],
   s: A):
      (sb[B]) => C
  =
  ((sb: sb[B]) =>
    (if (! (sbhdelemwell[B](sb)) &&
           ! (equal_set[channel](chandom[B](DUMMY[B]()), bot_set[channel])))
      bot_nc[C]
      else (Rep_cfun[C, C](conc[C](snd[A,
C]((dauttransition[A, sbelem[B], C,
                    Unit](aut)).apply(s).apply(sbhdelem[B](sb))))))(implicitly[bot_nc[C]],
                             implicitly[bot_nc[C]]).apply((tsexecstatesem_nc[A,
                                      B, C](aut,
     fst[A, C]((dauttransition[A, sbelem[B], C,
                                Unit](aut)).apply(s).apply(sbhdelem[B](sb))))).apply(sbdrop_nc[B](one_nat,
                   sb)))))

def tsexecsem[C, A : chan : enum : equal,
               B : bot_nc : conc](aut: dautomaton_ext[C, sbelem[A], B, Unit]):
      cfun[sb[A], B]
  =
  Abs_cfun[sb[A],
            B](((sb: sb[A]) =>
                 (Rep_cfun[B, B](conc[B](snd[C,
      B](dautinitconfig[C, sbelem[A], B,
                         Unit](aut)))))(implicitly[bot_nc[B]],
 implicitly[bot_nc[B]]).apply((tsexecstatesem_nc[C, A,
          B](aut, fst[C, B](dautinitconfig[C, sbelem[A], B,
    Unit](aut)))).apply(sb))))

def convertsem[A : tschan : enum : equal]:
      cfun[sb[A], stream[List[List[(A, M_pure)]]]]
  =
  tsexecsem[Unit, A, stream[List[List[(A, M_pure)]]]](convertaut[A])

def tolisthelper[A : countable](s: List[A], x1: event[A]):
      (List[A], stream[List[A]])
  =
  (s, x1) match {
  case (s, Tick()) => (Nil, sup[List[A]](s))
  case (s, Eventa(m)) => (s ++ List(m), stream_bottom_nc[List[A]]())
}

def sscanla_nc[A, B : countable,
                C : countable](f: A => B => (A, stream[C]), s: A,
                                x2: stream[B]):
      stream[C]
  =
  (f, s, x2) match {
  case (f, s, lscons_u_nc(a, b)) =>
    sconc_nc[C](snd[A, stream[C]]((f(s))(a)),
                 sscanla_nc[A, B, C](f, fst[A, stream[C]]((f(s))(a)), b))
  case (x, xa, stream_bottom_nc()) => stream_bottom_nc[C]()
}

def beoutchannelconstr(xa: Boolean): eventwithchan[channelsa] =
  Abs_eventwithchan[channelsa]((beoutchannel_rep(), booleventconstr(xa)))

def executableexpression_01(x0: Unit, x1: State, beInChannel_pattern: Boolean):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    List((Stateconstr(state_s()), List(beoutchannelconstr(true))))
}

def equal_substate(x0: Substate, x1: Substate): Boolean = (x0, x1) match {
  case (state_s(), state_t()) => false
  case (state_t(), state_s()) => false
  case (state_t(), state_t()) => true
  case (state_s(), state_s()) => true
}

def guard_01(x0: Unit, x1: State, beInChannel_pattern: Boolean): Boolean =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    equal_substate(s, state_s()) && equal_boola(beInChannel_pattern, true)
}

def executabletransitionh_01(x0: Unit, x1: State, beInChannel_pattern: Boolean):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    (if (guard_01((), Stateconstr(s), beInChannel_pattern))
      executableexpression_01((), Stateconstr(s), beInChannel_pattern) else Nil)
}

def executableexpression_00(x0: Unit, x1: State, beInChannel_pattern: Boolean):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    List((Stateconstr(state_s()), List(beoutchannelconstr(false))))
}

def guard_00(x0: Unit, x1: State, beInChannel_pattern: Boolean): Boolean =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    equal_substate(s, state_s()) && equal_boola(beInChannel_pattern, false)
}

def executabletransitionh_00(x0: Unit, x1: State, beInChannel_pattern: Boolean):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (x0, x1, beInChannel_pattern) match {
  case ((), Stateconstr(s), beInChannel_pattern) =>
    (if (guard_00((), Stateconstr(s), beInChannel_pattern))
      executableexpression_00((), Stateconstr(s), beInChannel_pattern) else Nil)
}

def executableeventtransition(para: Unit, state: State, x2: (channels, M_pure)):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (para, state, x2) match {
  case (para, state, (beinchannel_rep(), booleventconstr(beInChannel_pattern)))
    => executabletransitionh_00(para, state, beInChannel_pattern) ++
         executabletransitionh_01(para, state, beInChannel_pattern)
  case (uu, uv, (v, boolsyncconstr(vb))) => Nil
  case (uu, uv, (v, nateventconstr(vb))) => Nil
  case (uu, uv, (v, natsyncconstr(vb))) => Nil
  case (uu, uv, (v, stringeventconstr(vb))) => Nil
  case (uu, uv, (v, stringsyncconstr(vb))) => Nil
}

def eventtransition(p: Unit, s: State, i: (channels, M_pure)):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (if (nulla[(State,
               List[eventwithchan[channelsa]])](executableeventtransition(p, s,
                                   i)))
    List((s, Nil)) else executableeventtransition(p, s, i))

def executableexpressiont_1(x0: Unit, x1: State):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (x0, x1) match {
  case ((), Stateconstr(s)) =>
    List((Stateconstr(state_s()), List(beoutchannelconstr(true))))
}

def guardt_1(x0: Unit, x1: State): Boolean = (x0, x1) match {
  case ((), Stateconstr(s)) => equal_substate(s, state_s()) && true
}

def executabletransitionth_1(x0: Unit, x1: State):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (x0, x1) match {
  case ((), Stateconstr(s)) =>
    (if (guardt_1((), Stateconstr(s)))
      executableexpressiont_1((), Stateconstr(s)) else Nil)
}

def executableexpressiont_0(x0: Unit, x1: State):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (x0, x1) match {
  case ((), Stateconstr(s)) =>
    List((Stateconstr(state_s()), List(beoutchannelconstr(false))))
}

def guardt_0(x0: Unit, x1: State): Boolean = (x0, x1) match {
  case ((), Stateconstr(s)) => equal_substate(s, state_s()) && true
}

def executabletransitionth_0(x0: Unit, x1: State):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (x0, x1) match {
  case ((), Stateconstr(s)) =>
    (if (guardt_0((), Stateconstr(s)))
      executableexpressiont_0((), Stateconstr(s)) else Nil)
}

def executableticktransition(para: Unit, state: State):
      List[(State, List[eventwithchan[channelsa]])]
  =
  executabletransitionth_0(para, state) ++ executabletransitionth_1(para, state)

def ticktransition(p: Unit, s: State):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (if (nulla[(State,
               List[eventwithchan[channelsa]])](executableticktransition(p, s)))
    List((s, Nil)) else executableticktransition(p, s))

def ndatransition(p: Unit, s: State, x2: event[(channels, M_pure)]):
      List[(State, List[eventwithchan[channelsa]])]
  =
  (p, s, x2) match {
  case (p, s, Tick()) => ticktransition(p, s)
  case (p, s, Eventa(m)) => eventtransition(p, s, m)
}

def listeventwrapper[A, B,
                      C](f: (event[A]) => List[(B, List[C])], x1: event[A]):
      List[(B, List[event[C]])]
  =
  (f, x1) match {
  case (f, Tick()) =>
    map[(B, List[C]),
         (B, List[event[C]])](((a: (B, List[C])) =>
                                apsnd[List[C], List[event[C]],
                                       B](((ls: List[C]) =>
    Tick[C]() :: map[C, event[C]](((aa: C) => Eventa[C](aa)), ls)),
   a)),
                               f(Tick[A]()))
  case (f, Eventa(v)) =>
    map[(B, List[C]),
         (B, List[event[C]])](((a: (B, List[C])) =>
                                apsnd[List[C], List[event[C]],
                                       B](((aa: List[C]) =>
    map[C, event[C]](((ab: C) => Eventa[C](ab)), aa)),
   a)),
                               f(Eventa[A](v)))
}

def transition(p: Unit, s: State):
      (event[(channels, M_pure)]) => List[(State, sb[channelsa])]
  =
  comp[List[(State, List[event[eventwithchan[channelsa]]])],
        List[(State, sb[channelsa])],
        event[(channels,
                M_pure)]](((a: List[(State,
                                      List[event[eventwithchan[channelsa]]])])
                             =>
                            map[(State, List[event[eventwithchan[channelsa]]]),
                                 (State,
                                   sb[channelsa])](((aa:
               (State, List[event[eventwithchan[channelsa]]]))
              =>
             apsnd[List[event[eventwithchan[channelsa]]], sb[channelsa],
                    State](comp[stream[event[eventwithchan[channelsa]]],
                                 sb[channelsa],
                                 List[event[eventwithchan[channelsa]]]](Rep_cfun[stream[event[eventwithchan[channelsa]]],
  sb[channelsa]](ssplit[channelsa]),
                                 ((ab: List[event[eventwithchan[channelsa]]]) =>
                                   list2s[event[eventwithchan[channelsa]]](ab))),
                            aa)),
            a)),
                           ((a: event[(channels, M_pure)]) =>
                             listeventwrapper[(channels, M_pure), State,
       eventwithchan[channelsa]](((aa: event[(channels, M_pure)]) =>
                                   ndatransition(p, s, aa)),
                                  a)))

def executableinitialconfigs:
      Unit => List[(State, List[eventwithchan[channelsa]])]
  =
  ((a: Unit) => {
                  val (): Unit = a;
                  List((Stateconstr(state_s()), Nil))
                })

def configc(p: Unit): List[(State, List[eventwithchan[channelsa]])] =
  (if (nulla[(State,
               List[eventwithchan[channelsa]])](executableinitialconfigs.apply(p)))
    List((rnd[State]((natural_of_integer(BigInt(2)),
                       natural_of_integer(BigInt(3)))),
           Nil))
    else executableinitialconfigs.apply(p))

def config(p: Unit): List[(State, sb[channelsa])] =
  (if (true)
    map[(State, List[event[eventwithchan[channelsa]]]),
         (State,
           sb[channelsa])](((a: (State, List[event[eventwithchan[channelsa]]]))
                              =>
                             apsnd[List[event[eventwithchan[channelsa]]],
                                    sb[channelsa],
                                    State](comp[stream[event[eventwithchan[channelsa]]],
         sb[channelsa],
         List[event[eventwithchan[channelsa]]]](Rep_cfun[stream[event[eventwithchan[channelsa]]],
                  sb[channelsa]](ssplit[channelsa]),
         ((aa: List[event[eventwithchan[channelsa]]]) =>
           list2s[event[eventwithchan[channelsa]]](aa))),
    a)),
                            map[(State, List[eventwithchan[channelsa]]),
                                 (State,
                                   List[event[eventwithchan[channelsa]]])](((a:
                                       (State, List[eventwithchan[channelsa]]))
                                      =>
                                     apsnd[List[eventwithchan[channelsa]],
    List[event[eventwithchan[channelsa]]],
    State](((ls: List[eventwithchan[channelsa]]) =>
             map[eventwithchan[channelsa],
                  event[eventwithchan[channelsa]]](((aa:
               eventwithchan[channelsa])
              =>
             Eventa[eventwithchan[channelsa]](aa)),
            ls) ++
               List(Tick[eventwithchan[channelsa]]())),
            a)),
                                    configc(p)))
    else map[(State, List[event[eventwithchan[channelsa]]]),
              (State,
                sb[channelsa])](((a: (State,
                                       List[event[eventwithchan[channelsa]]]))
                                   =>
                                  apsnd[List[event[eventwithchan[channelsa]]],
 sb[channelsa],
 State](comp[stream[event[eventwithchan[channelsa]]], sb[channelsa],
              List[event[eventwithchan[channelsa]]]](Rep_cfun[stream[event[eventwithchan[channelsa]]],
                       sb[channelsa]](ssplit[channelsa]),
              ((aa: List[event[eventwithchan[channelsa]]]) =>
                list2s[event[eventwithchan[channelsa]]](aa))),
         a)),
                                 map[(State, List[eventwithchan[channelsa]]),
                                      (State,
List[event[eventwithchan[channelsa]]])](((a:
    (State, List[eventwithchan[channelsa]]))
   =>
  apsnd[List[eventwithchan[channelsa]], List[event[eventwithchan[channelsa]]],
         State](((aa: List[eventwithchan[channelsa]]) =>
                  map[eventwithchan[channelsa],
                       event[eventwithchan[channelsa]]](((ab:
                    eventwithchan[channelsa])
                   =>
                  Eventa[eventwithchan[channelsa]](ab)),
                 aa)),
                 a)),
 configc(p))))

def laut(p: Unit):
      listautomaton_ext[State, event[(channels, M_pure)], sb[channelsa], Unit]
  =
  listautomaton_exta[State, event[(channels, M_pure)], sb[channelsa],
                      Unit](((a: State) => transition(p, a)), config(p), ())

def tstimedtoorigin[A : one_chan](x0: tstimed[A]): A = x0 match {
  case TSTIMEDA(cs) => cs
}

def seventtolist_nc[A : countable](s: stream[event[A]]): stream[List[A]] =
  sscanla_nc[List[A], event[A],
              List[A]](((a: List[A]) => (b: event[A]) => tolisthelper[A](a, b)),
                        Nil, s)

def inconv_nc[A : echan : enum](sb: sb[A]): sb[tstimed[A]] =
  Abs_sb[tstimed[A]](((c: tstimed[A]) =>
                       smap_nc[List[M_pure],
                                M](comp[M_timed, M,
 List[M_pure]](((a: M_timed) => Timed(a)), ((a: List[M_pure]) => Tfin(a))),
                                    seventtolist_nc[M_pure](smap_nc[M,
                             event[M_pure]](((a: M) => m2event(a)),
     sbgetch_nc[A, A](tstimedtoorigin[A](c), sb))))))

def execstatesem_nc[A, B : countable,
                     C : bot_nc : conc](aut: dautomaton_ext[A, B, C, Unit],
 s: A, x2: stream[B]):
      C
  =
  (aut, s, x2) match {
  case (aut, s, lscons_u_nc(a, rt)) =>
    (Rep_cfun[C, C](conc[C](snd[A, C]((dauttransition[A, B, C,
               Unit](aut)).apply(s).apply(a)))))(implicitly[bot_nc[C]],
          implicitly[bot_nc[C]]).apply(execstatesem_nc[A, B,
                C](aut, fst[A, C]((dauttransition[A, B, C,
           Unit](aut)).apply(s).apply(a)),
                    rt))
  case (aut, s, stream_bottom_nc()) => bot_nc[C]
}

def execsem_nc[A, B : countable,
                C : bot_nc : conc](aut: dautomaton_ext[A, B, C, Unit],
                                    s: stream[B]):
      C
  =
  (Rep_cfun[C, C](conc[C](snd[A, C](dautinitconfig[A, B, C,
            Unit](aut)))))(implicitly[bot_nc[C]],
                            implicitly[bot_nc[C]]).apply(execstatesem_nc[A, B,
                                  C](aut, fst[A,
       C](dautinitconfig[A, B, C, Unit](aut)),
                                      s))

def execmergesem_nc[A : countable : equal](seed: (natural, natural),
    s: stream[List[List[A]]]):
      stream[List[A]]
  =
  execsem_nc[(Unit, (natural, natural)), List[List[A]],
              stream[List[A]]](exectoda[Unit, List[List[A]],
 stream[List[A]]](listtoexec[Unit, List[List[A]], stream[List[A]]](mergeaut[A]),
                   seed),
                                s)

def slisttoevent_nc[A : countable](x0: stream[List[A]]): stream[event[A]] = x0
  match {
  case lscons_u_nc(x :: xs, s) =>
    sconc_nc[event[A]](sup[event[A]](Eventa[A](x)),
                        slisttoevent_nc[A](sconc_nc[List[A]](sup[List[A]](xs),
                      s)))
  case lscons_u_nc(Nil, s) =>
    sconc_nc[event[A]](sup[event[A]](Tick[A]()), slisttoevent_nc[A](s))
  case stream_bottom_nc() => stream_bottom_nc[event[A]]()
}

def execbmerge[A : echan : enum : equal](seed: (natural, natural), sb: sb[A]):
      eventwellstream[A]
  =
  Abs_eventwellstream[A](emap_nc[(tstimed[A], M_pure),
                                  (A, M_pure)](((a: (tstimed[A], M_pure)) =>
         {
           val (c, aa): (tstimed[A], M_pure) = a;
           (tstimedtoorigin[A](c), aa)
         }),
        slisttoevent_nc[(tstimed[A],
                          M_pure)](execmergesem_nc[(tstimed[A],
             M_pure)](seed,
                       (Rep_cfun[sb[tstimed[A]],
                                  stream[List[List[(tstimed[A],
             M_pure)]]]](convertsem[tstimed[A]])).apply(inconv_nc[A](sb))))))

def Rep_eventwellstream[A : chan : countable](x0: eventwellstream[A]):
      stream[event[(A, M_pure)]]
  =
  x0 match {
  case Abs_eventwellstream(x) => x
}

def execsem(x0: (Unit, ((natural, natural), (natural, natural))),
             sb: sb[channels]):
      sb[channelsa]
  =
  (x0, sb) match {
  case ((p, (seed1, seed2)), sb) =>
    execsem_nc[(State, (natural, natural)), event[(channels, M_pure)],
                sb[channelsa]](exectoda[State, event[(channels, M_pure)],
 sb[channelsa]](listtoexec[State, event[(channels, M_pure)],
                            sb[channelsa]](laut(p)),
                 seed1),
                                Rep_eventwellstream[channels](execbmerge[channels](seed2,
    sb)))
}

def sb2stream(a: sb[channelsa]): stream[event[Boolean]] =
  (Rep_cfun[sb[channelsa], stream[event[Boolean]]](sbgetter)).apply(a)

}
