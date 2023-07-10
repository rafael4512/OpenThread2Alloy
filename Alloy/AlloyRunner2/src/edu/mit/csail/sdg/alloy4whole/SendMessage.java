package edu.mit.csail.sdg.alloy4whole;
import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.net.URLConnection;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;


public class SendMessage {
    /**
     * Telegram Bot to send notifications.
     * @param text message to send
     */
    public static void sendToTelegram(String text) {
        String urlString = "https://api.telegram.org/bot%s/sendMessage?chat_id=%s&text=%s";

        //Add Telegram token (given Token is fake)
        String apiToken = "5800717192:AAHGUMy3coOYiAks1jVz4qItoWzCrFfB0QI";

        //Add chatId (given chatId is fake)
        String chatId = "1449543557";
        //String text = "Hello world!";

        //text -> need to be encoded because it can have spaces.
        urlString = String.format(urlString, apiToken, chatId, URLEncoder.encode(text, StandardCharsets.UTF_8));

        try {
            URL url = new URL(urlString);
            URLConnection conn = url.openConnection();
            InputStream is = new BufferedInputStream(conn.getInputStream());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}