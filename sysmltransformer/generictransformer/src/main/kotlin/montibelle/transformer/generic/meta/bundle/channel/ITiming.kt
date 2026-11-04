package montibelle.transformer.generic.meta.bundle.channel

interface ITiming {
  val name: String
  val isEventBased: Boolean
    get() = false

  val isTimeSyncronous: Boolean
    get() = false

  val isStrictlyTimeSyncronous : Boolean
    get() = false
}
