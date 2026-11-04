package montibelle.transformer.generic.meta.bundle;

import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.focus._symboltable.TimingSymbol;
import montibelle.transformer.generic.meta.IIdentifiable;

import java.util.List;

public interface IBundle extends IIdentifiable {

  List<ChannelSymbol> getChannels();

  TimingSymbol getTimingSymbol();

}
