package math;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import org.apache.camel.CamelContext;
import org.apache.camel.Exchange;
import org.apache.camel.Processor;
import org.apache.camel.builder.RouteBuilder;
import org.apache.camel.component.seda.SedaComponent;
import org.apache.camel.impl.DefaultCamelContext;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class ApiServer {
    public ApiServer() {

    }
    void run() {
        CamelContext context = new DefaultCamelContext();
        try { configQueue(context);
            context.addRoutes(new RouteBuilder() {
                public void configure() { //</p><p>e.g. curl -X POST "https://api.londonoo.com:8888" -d "city=london&date=2022-05-01"</p></div></body></html>
                    from("jetty:http://0.0.0.0:8888/").to("sedaComponent:request?timeout=0&concurrentConsumers=3");
                    from("sedaComponent:request").process(new RestRequestProcessor());}});
            context.start();
            while (true) {
                try {
                    Thread.sleep(10000L);
                } catch (InterruptedException ignored) {}
            }
        }
        catch (Exception ignored){
        } finally {
            context.stop();
        }
    }

    static class RestRequestProcessor implements Processor {
        public void process(Exchange exchange)  {
            try {
                String def = exchange.getIn().getHeader("def", String.class);
                String txt = Files.readString(Path.of("combined-" + def + "_2-2.txt"));
                String response = "";
                List<Lemma> lemmas = new ArrayList<>();
                if (!Util.empty(txt)){
                    txt = txt.substring(2);
                    for (String lemma : txt.split("\n\n\n")) {
                        String[] split = lemma.split("\n\n");
                        if (split.length == 3){
                            List<String> defined = Arrays.asList(split[1].split("\n"));
                            lemmas.add(new Lemma(split[0], defined, split[2]));
                        }
                    }

                    Gson gson = new GsonBuilder().setPrettyPrinting().create();
                    response = gson.toJson(lemmas);
                }
                exchange.getIn().setBody(response + "\n");
            } catch (Exception ignored){}
        }
    }
    record Lemma (String lemma, List<String> defined, String statement){}

    void configQueue(CamelContext ctx) {
        SedaComponent c = new SedaComponent();
        c.setQueueSize(3);
        ctx.addComponent("sedaComponent", c);
    }
}