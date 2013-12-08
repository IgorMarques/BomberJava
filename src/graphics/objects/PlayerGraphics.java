package graphics.objects;


import game_objects.GameObject;
import game_objects.Player;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;

import static constants.Constants.*;

public class PlayerGraphics extends GameObjectGraphics {

	private Player player;
	
	public PlayerGraphics(GameObject player) {
		super(player);
		this.player = (Player) player;
	}
	
	public void draw(Graphics g) {
		Graphics2D g2d = (Graphics2D) g;
		g2d.setColor(player.isDead() ? Color.red : Color.blue);
		
		//g2d.fillRect(player.getX() * TILESIZE, player.getY() * TILESIZE, 32, 32);
		g2d.setColor(Color.black);
		
		BufferedImage img = null;
		String url = System.getProperty("user.dir");
		url+="/src/sprites/character1.gif";
		
		try {
		    img = ImageIO.read(new File(url));
		} catch (IOException e) {
		}
		g2d.drawImage(img, player.getX() * TILESIZE, player.getY() * TILESIZE, null);
	}
}
