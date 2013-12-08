package graphics.objects;

import game_objects.Map;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;

import static constants.Constants.*;

public class MapGraphics implements Drawable {

	private Map map;

	public MapGraphics(Map map) {
		this.map = map;
	}
	
	public void draw(Graphics g) {
		g.setColor(Color.BLACK);
		BufferedImage img = null;
		String url = System.getProperty("user.dir");
		url+="/src/sprites/grass.gif";
		
		try {
		    img = ImageIO.read(new File(url));
		} catch (IOException e) {
		}
		
		for (int i = 0; i < map.getHeight(); i++) {
			for (int j = 0; j < map.getWidth(); j++) {
				//g.drawRect(j * TILESIZE, i * TILESIZE, TILESIZE, TILESIZE);
				g.drawImage(img, j * TILESIZE, i * TILESIZE, null);
			}
		}
	}

}
