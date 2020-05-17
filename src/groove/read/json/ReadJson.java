package groove.read.json;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;

import com.alexmerz.graphviz.ParseException;

@SuppressWarnings({ "unused", "deprecation" })
public class ReadJson {

	public static void main(String[] args) {

		JSONParser parser = new JSONParser();

		try {

			FileReader reader = new FileReader("Sample.json");
			Object obj = null;
			try {
				obj = parser.parse(reader);
			} catch (org.json.simple.parser.ParseException e) {

				e.printStackTrace();
			}
			JSONArray array = (JSONArray) obj;
			System.out.println(array);

		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}

	}

}
